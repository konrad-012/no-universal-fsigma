#!/usr/bin/env python3
"""Check the submitted sources; --compiler also audits Challenge's import closure."""
import argparse
import json
import os
from pathlib import Path
import re
import subprocess
import sys

ROOT = Path(__file__).resolve().parents[1]
AXIOMS = {"propext", "Classical.choice", "Quot.sound"}
THEOREM = "NoUniversalFSigma.not_isUniversalFSigma"


def fail(message):
    raise SystemExit(message)


def run(*arguments):
    return subprocess.check_output(arguments, cwd=ROOT, text=True).strip()


def code_only(text, keep_doc_markers=False):
    """Blank nested comments and string literals, preserving line positions."""
    result = list(text)
    index = 0
    while index < len(text):
        start = index
        doc = False
        if text.startswith("--", index):
            end = text.find("\n", index)
            index = len(text) if end < 0 else end
        elif text.startswith("/-", index):
            doc = text.startswith(("/--", "/-!"), index)
            index += 2
            depth = 1
            while index < len(text) and depth:
                if text.startswith("/-", index):
                    depth += 1
                    index += 2
                elif text.startswith("-/", index):
                    depth -= 1
                    index += 2
                else:
                    index += 1
        elif text[index] == '"':
            index += 1
            while index < len(text):
                if text[index] == "\\":
                    index += 2
                elif text[index] == '"':
                    index += 1
                    break
                else:
                    index += 1
        else:
            index += 1
            continue
        for position in range(start, min(index, len(text))):
            if result[position] not in "\r\n":
                result[position] = " "
        if doc and keep_doc_markers:
            result[start] = "!"
    return "".join(result)


def source_files():
    files = []
    for directory, children, names in os.walk(ROOT, followlinks=False):
        children[:] = sorted(name for name in children if name not in {".git", ".lake"}
                             and not (Path(directory) / name).is_symlink())
        files.extend(Path(directory) / name for name in sorted(names) if name.endswith(".lean"))
    return files


def check_config():
    config = json.loads((ROOT / "comparator.json").read_text())
    expected = {
        "challenge_module": "Challenge", "solution_module": "Solution",
        "theorem_names": [THEOREM], "definition_names": [],
    }
    if any(config.get(key) != value for key, value in expected.items()):
        fail("comparator.json must compare exactly the advertised theorem, with no definition holes")
    if set(config.get("permitted_axioms", [])) != AXIOMS:
        fail("comparator.json must permit exactly the three standard Lean axioms")
    if set(config) - set(expected) - {"permitted_axioms", "enable_nanoda"}:
        fail("comparator.json contains an unsupported field (external_kernels is verifier-owned)")


def check_sources():
    files = source_files()
    for required in ["Challenge.lean", "Solution.lean", "NoUniversalFSigma.lean"]:
        if ROOT / required not in files:
            fail(f"Missing {required}")
    for path in files:
        relative = path.relative_to(ROOT)
        if path.is_symlink() or not path.is_file():
            fail(f"{relative}: Lean sources must be regular files")
        raw = path.read_bytes()
        text = raw.decode("utf-8")
        lines = text.count("\n") + int(bool(text) and not text.endswith("\n"))
        if lines > 10_000:
            fail(f"{relative}: exceeds the 10,000-line source limit")
        if path.name != "lakefile.lean" and not re.match(
                r"[ \r\n]*module\b", code_only(text, keep_doc_markers=True)):
            fail(f"{relative}: must begin with module (before documentation)")
        if path == ROOT / "Challenge.lean":
            if lines > 1_000 or len(raw) > 100 * 1024:
                fail("Challenge.lean exceeds its 1,000-line / 100-KiB limit")
        else:
            forbidden = re.search(r"\b(sorry|admit|sorryAx|axiom|native_decide)\b", code_only(text))
            if forbidden:
                line = text.count("\n", 0, forbidden.start()) + 1
                fail(f"{relative}:{line}: forbidden proof token {forbidden.group()}")
    check_config()
    return files


def headers(paths):
    data = json.loads(run("lake", "env", "lean", "--deps-json", *map(str, paths)))
    entries = data["imports"]
    if len(entries) != len(paths):
        fail("Lean returned an unexpected dependency report")
    for path, entry in zip(paths, entries):
        if entry.get("errors") or "result" not in entry:
            fail(f"{path}: Lean could not parse its import header: {entry.get('errors')}")
    return [entry["result"] for entry in entries]


def compiler_checks(files):
    own = [path for path in files if path.name != "lakefile.lean"]
    for start in range(0, len(own), 128):
        batch = own[start:start + 128]
        for path, result in zip(batch, headers(batch)):
            if not result["isModule"]:
                fail(f"{path.relative_to(ROOT)}: Lean does not recognize a module header")

    # Trust the pinned Mathlib closure, not arbitrary additional Solution dependencies.
    manifest = json.loads((ROOT / "lake-manifest.json").read_text())
    packages = {entry["name"]: entry for entry in manifest["packages"]}
    package_dir = ROOT / manifest.get("packagesDir", ".lake/packages")
    mathlib = package_dir / "mathlib"
    mathlib_manifest = json.loads((mathlib / "lake-manifest.json").read_text())
    trusted = {"mathlib": packages["mathlib"]}
    for entry in mathlib_manifest["packages"]:
        actual = packages.get(entry["name"])
        if actual is None or (actual.get("rev"), actual.get("url")) != (
                entry.get("rev"), entry.get("url")):
            fail(f"Mathlib dependency pin mismatch: {entry['name']}")
        trusted[entry["name"]] = actual
    trusted_roots = []
    for name, entry in trusted.items():
        path = (package_dir / name).resolve()
        if entry.get("type") != "git" or run("git", "-C", str(path), "rev-parse", "HEAD") != entry["rev"]:
            fail(f"The trusted dependency is not at its manifest Git pin: {name}")
        trusted_roots.append(path)
    prefix = Path(run("lean", "--print-prefix")).resolve()
    core = prefix / "src/lean"
    trusted_roots.append(core)
    search = [Path(part).resolve() for part in run("lake", "env", "printenv", "LEAN_SRC_PATH").split(os.pathsep)
              if part] + [core]

    pending = [entry["module"] for entry in headers([ROOT / "Challenge.lean"])[0]["imports"]]
    visited = set()
    while pending:
        paths = []
        while pending and len(paths) < 128:
            module = pending.pop()
            if module in visited:
                continue
            visited.add(module)
            relative = Path(*module.split(".")).with_suffix(".lean")
            path = next((base / relative for base in search if (base / relative).is_file()), None)
            if path is None:
                fail(f"Cannot locate Challenge dependency source: {module}")
            path = path.resolve()
            if not any(path.is_relative_to(base) for base in trusted_roots):
                fail(f"Challenge depends on an untrusted local or proof module: {module} ({path})")
            paths.append(path)
        if paths:
            for result in headers(paths):
                pending.extend(entry["module"] for entry in result["imports"])
    print(f"Challenge import closure: {len(visited)} pinned Mathlib/core modules")


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--compiler", action="store_true")
    options = parser.parse_args()
    files = check_sources()
    if options.compiler:
        compiler_checks(files)
    print(f"Source and single-theorem configuration checks passed ({len(files)} Lean files)")


if __name__ == "__main__":
    try:
        main()
    except (OSError, ValueError, KeyError, subprocess.CalledProcessError) as error:
        sys.exit(f"Source check failed: {error}")
