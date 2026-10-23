# There is no universal Fσ equivalence relation

This project formalizes the nonuniversality conclusion of Ruijun Wang's
[There is no universal Fσ equivalence relation](https://arxiv.org/abs/2610.31052v1).

For every equivalence relation `E` whose graph is an Fσ subset of the product of
a Polish space with itself, there is an equivalence relation `F` with an Fσ graph
on another Polish space such that `F` is not Borel reducible to `E`. Both spaces
carry the Borel sigma algebras of their specified topologies. A Borel reduction
is a measurable map that preserves and reflects equivalence.

The single advertised theorem is `NoUniversalFSigma.not_isUniversalFSigma`.
The proof follows Wang's construction using Hilbert spaces, algebraic spans,
tensor constructions, and transfinite ranks. Its internal construction supplies
coset relations of real linear subspaces of a Hilbert space.

## Statement and proof

- `Challenge.lean` independently defines the mathematical notions and states the
  theorem. It imports only Mathlib and has one deliberate `sorry` for its proof.
  This is the statement a reader should audit.
- `Solution.lean` states the same theorem and connects it to the completed proof.
- `NoUniversalFSigma/` contains the definitions and proof development. It has no
  dependency on another project containing this formalization.
- `comparator.json` selects this one theorem, leaves no definition holes, and
  permits only `propext`, `Quot.sound`, and `Classical.choice`.
- `formalization.yaml` records the source, scope, authorship, automation, and
  review status.

The project pins Lean and Mathlib to `v4.35.0-rc2`. The committed Lake manifest
records exact dependency revisions. Generated build output is not source.

## Check locally

From the repository root, with the pinned Lean toolchain installed:

```sh
lake exe cache get
scripts/check.sh
scripts/check-comparator.sh
```

The first check builds the development and checks proof axioms. The Comparator
check compares the independent Challenge with the Solution, enforces the
permitted axioms, and rechecks the exported proof with Lean and independent
kernel checkers. Its sandbox requires bubblewrap and working unprivileged user
namespaces on Linux. The script reports missing prerequisites rather than
falling back to an unsandboxed run.

The Challenge's `declaration uses sorry` warning is intentional. A proof in the
Solution or its dependencies must not rely on `sorryAx`.

Local verification on 2026-10-23 passed both scripts. Comparator matched the
independent statement and its concrete definitions, and Lean, NanoDa, and
con-ron accepted the exported solution. The theorem uses only the three axioms
listed above. Palomar's own source, metadata, configuration, and toolchain
validators also accepted this layout. These checks do not constitute a Palomar
submission or registration.

## Provenance and review

The mathematical result and construction are due to Ruijun Wang. This is a
source-based formalization, not a claim of a new mathematical result. The code
was generated and revised by Codex agents under human direction. Exact model
variants and costs were not recorded.

Agent statement audits and mechanical checks have informed the development.
No independent human peer review or endorsement by the paper's author is
claimed. Mechanical checking establishes the formal proof of the formal
statement; readers should also examine whether the definitions and statement
express the intended mathematics.

## Palomar

The repository uses the Challenge/Solution layout described by the
[Palomar submission guide](https://palomar-registry.org/how-to-submit).
[Palomar](https://palomar-registry.org/about) records a fixed public repository
commit, mechanical verification, provenance, and an automated review. It does
not replace expert review. This repository has not been submitted or registered
by its preparation here. A future submission goes through
[the Palomar submission service](https://submit.palomar-registry.org/) and must
identify the exact public commit to check.

The formalization code is distributed under the MIT license in `LICENSE`.
The cited paper and external dependencies retain their own licenses.
