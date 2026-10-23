module

public import Mathlib

@[expose] public section

/-! # The Hilbert-coordinate branch family

The coordinate realization of Section 5. A node is represented by its length and its finite
sequence of digits; `none` labels its marker coordinate and `some n` its signed coordinate.
The estimates below use absolute convergence, so do not require orthogonality calculations.
-/

noncomputable section

open Set Filter Topology
open scoped ENNReal lp

namespace NoUniversalFSigma.Proof.Branch

abbrev Point := ℕ → ℕ
abbrev Node := Σ n : ℕ, Fin n → ℕ
abbrev Coord := Node × Option ℕ
abbrev Space := ℓ²(Coord, ℝ)

def nodePrefix (x : Point) (n : ℕ) : Node := ⟨n, fun i => x i⟩

@[simp] lemma nodePrefix_fst (x : Point) (n : ℕ) : (nodePrefix x n).1 = n := rfl

def Cylinder (s : Node) : Set Point := {x | nodePrefix x s.1 = s}

def weight (s : Node) : ℝ := ∏ i : Fin s.1, (1 / 2 : ℝ) ^ (s.2 i + 2)

lemma weight_pos (s : Node) : 0 < weight s := by
  exact Finset.prod_pos fun i _ => pow_pos (by norm_num) _

lemma weight_ne_zero (s : Node) : weight s ≠ 0 := ne_of_gt (weight_pos s)

@[simp] lemma weight_empty (x : Point) : weight (nodePrefix x 0) = 1 := by
  change (∏ i : Fin 0, (1 / 2 : ℝ) ^ (x i + 2)) = 1
  simp

lemma weight_nodePrefix_succ (x : Point) (n : ℕ) :
    weight (nodePrefix x (n + 1)) = weight (nodePrefix x n) * (1 / 2 : ℝ) ^ (x n + 2) := by
  change (∏ i : Fin (n + 1), (1 / 2 : ℝ) ^ (x i + 2)) =
    (∏ i : Fin n, (1 / 2 : ℝ) ^ (x i + 2)) * (1 / 2 : ℝ) ^ (x n + 2)
  rw [Fin.prod_univ_castSucc]
  rfl

lemma digit_weight_le (k : ℕ) : (1 / 2 : ℝ) ^ (k + 2) ≤ 1 / 4 := by
  rw [pow_add]
  have h := pow_le_one₀ (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num : (1 / 2 : ℝ) ≤ 1) (n := k)
  nlinarith

lemma weight_nodePrefix_le (x : Point) (n : ℕ) : weight (nodePrefix x n) ≤ (1 / 4 : ℝ) ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [weight_nodePrefix_succ, pow_succ (1 / 4 : ℝ) n]
    exact mul_le_mul ih (digit_weight_le _) (by positivity) (by positivity)

lemma weight_nodePrefix_add_le (x : Point) (n m : ℕ) :
    weight (nodePrefix x (n + m)) ≤ weight (nodePrefix x n) * (1 / 4 : ℝ) ^ m := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Nat.add_succ, weight_nodePrefix_succ, pow_succ (1 / 4 : ℝ) m, ← mul_assoc]
    exact mul_le_mul ih (digit_weight_le _) (by positivity)
      (mul_nonneg (weight_pos _).le (by positivity))

def sign (k : ℕ) : ℝ := if k % 2 = 0 then 1 else -1

@[simp] lemma abs_sign (k : ℕ) : |sign k| = 1 := by
  unfold sign
  split_ifs <;> norm_num

@[simp] lemma norm_sign (k : ℕ) : ‖sign k‖ = 1 := by simp [Real.norm_eq_abs]

/-- The two-coordinate contribution at level `n`. -/
def term (x : Point) (n : ℕ) : Space :=
  lp.single 2 (nodePrefix x n, none) (weight (nodePrefix x n)) +
    lp.single 2 (nodePrefix x n, some (x n / 2)) (weight (nodePrefix x n) * sign (x n))

lemma norm_term_le (x : Point) (n : ℕ) : ‖term x n‖ ≤ 2 * weight (nodePrefix x n) := by
  refine (norm_add_le _ _).trans ?_
  simp only [lp.norm_single (by norm_num : (0 : ℝ≥0∞) < 2), Real.norm_eq_abs, abs_mul, abs_sign, mul_one,
    abs_of_pos (weight_pos _)]
  linarith

lemma norm_term_le_geometric (x : Point) (n : ℕ) :
    ‖term x n‖ ≤ 2 * (1 / 4 : ℝ) ^ n :=
  (norm_term_le x n).trans (mul_le_mul_of_nonneg_left (weight_nodePrefix_le x n) (by norm_num))

lemma summable_norm_term (x : Point) : Summable (fun n => ‖term x n‖) := by
  exact Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (norm_term_le_geometric x)
    ((summable_geometric_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 4)
      (by norm_num : (1 / 4 : ℝ) < 1)).mul_left 2)

lemma summable_term (x : Point) : Summable (term x) := (summable_norm_term x).of_norm

/-- Wang's branch vector, as a norm-convergent series in the real Hilbert space. -/
def j (x : Point) : Space := ∑' n, term x n

lemma norm_j_le (x : Point) : ‖j x‖ ≤ 8 / 3 := by
  calc
    ‖j x‖ ≤ ∑' n, ‖term x n‖ := norm_tsum_le_tsum_norm (summable_norm_term x)
    _ ≤ ∑' n : ℕ, 2 * (1 / 4 : ℝ) ^ n := (summable_norm_term x).tsum_le_tsum
      (norm_term_le_geometric x)
      ((summable_geometric_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 4)
        (by norm_num : (1 / 4 : ℝ) < 1)).mul_left 2)
    _ = 8 / 3 := by
      rw [tsum_mul_left, tsum_geometric_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 4)
        (by norm_num : (1 / 4 : ℝ) < 1)]
      norm_num

lemma nodePrefix_level_eq {x : Point} {n : ℕ} {s : Node} (h : nodePrefix x n = s) : n = s.1 :=
  congrArg Sigma.fst h

lemma term_apply_of_ne_level (x : Point) (n : ℕ) (c : Coord) (h : n ≠ c.1.1) :
    term x n c = 0 := by
  have hnode : nodePrefix x n ≠ c.1 := fun he => h (nodePrefix_level_eq he)
  simp [term, lp.single_apply, Prod.ext_iff, hnode]

lemma j_apply (x : Point) (c : Coord) : j x c = term x c.1.1 c := by
  change (lp.evalCLM ℝ (fun _ : Coord => ℝ) 2 c) (∑' n, term x n) = _
  rw [(lp.evalCLM ℝ (fun _ : Coord => ℝ) 2 c).map_tsum (summable_term x)]
  exact tsum_eq_single c.1.1 (fun n hn => term_apply_of_ne_level x n c hn)

lemma nodePrefix_eq_iff (x : Point) (s : Node) : nodePrefix x s.1 = s ↔ ∀ i : Fin s.1, x i = s.2 i := by
  cases s with
  | mk n s => simp [nodePrefix, funext_iff]

lemma j_marker (x : Point) (s : Node) :
    j x (s, none) = if nodePrefix x s.1 = s then weight s else 0 := by
  rw [j_apply]
  by_cases h : nodePrefix x s.1 = s
  · simp [term, h, lp.single_apply]
  · simp [term, h, lp.single_apply, Prod.ext_iff]

lemma j_signed (x : Point) (s : Node) (k : ℕ) :
    j x (s, some k) =
      if nodePrefix x s.1 = s ∧ x s.1 / 2 = k then weight s * sign (x s.1) else 0 := by
  rw [j_apply]
  by_cases h : nodePrefix x s.1 = s
  · simp [term, h, lp.single_apply, Pi.single_apply, Prod.ext_iff, eq_comm]
  · simp [term, h, lp.single_apply, Prod.ext_iff]

/-- The branch tail after the first `n` levels. -/
def tail (x : Point) (n : ℕ) : Space := ∑' m : ℕ, term x (m + n)

lemma norm_term_add_le (x : Point) (n m : ℕ) :
    ‖term x (m + n)‖ ≤ (2 * weight (nodePrefix x n)) * (1 / 4 : ℝ) ^ m := by
  have h := (norm_term_le x (n + m)).trans
    (mul_le_mul_of_nonneg_left (weight_nodePrefix_add_le x n m) (by norm_num))
  simpa only [Nat.add_comm m n, mul_assoc] using h

lemma summable_norm_tail (x : Point) (n : ℕ) :
    Summable fun m => ‖term x (m + n)‖ := by
  exact Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (norm_term_add_le x n)
    ((summable_geometric_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 4)
      (by norm_num : (1 / 4 : ℝ) < 1)).mul_left (2 * weight (nodePrefix x n)))

lemma norm_tail_le (x : Point) (n : ℕ) :
    ‖tail x n‖ ≤ (8 / 3 : ℝ) * weight (nodePrefix x n) := by
  calc
    ‖tail x n‖ ≤ ∑' m, ‖term x (m + n)‖ := norm_tsum_le_tsum_norm (summable_norm_tail x n)
    _ ≤ ∑' m : ℕ, (2 * weight (nodePrefix x n)) * (1 / 4 : ℝ) ^ m :=
      (summable_norm_tail x n).tsum_le_tsum (norm_term_add_le x n)
        ((summable_geometric_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 4)
          (by norm_num : (1 / 4 : ℝ) < 1)).mul_left (2 * weight (nodePrefix x n)))
    _ = (8 / 3 : ℝ) * weight (nodePrefix x n) := by
      rw [tsum_mul_left, tsum_geometric_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 4)
        (by norm_num : (1 / 4 : ℝ) < 1)]
      ring

lemma initial_add_tail (x : Point) (n : ℕ) :
    (∑ m ∈ Finset.range n, term x m) + tail x n = j x :=
  (summable_term x).sum_add_tsum_nat_add n

lemma tail_apply (x : Point) (n : ℕ) (c : Coord) :
    tail x n c = if n ≤ c.1.1 then j x c else 0 := by
  change (lp.evalCLM ℝ (fun _ : Coord => ℝ) 2 c) (∑' m : ℕ, term x (m + n)) = _
  rw [(lp.evalCLM ℝ (fun _ : Coord => ℝ) 2 c).map_tsum (summable_norm_tail x n).of_norm]
  change (∑' m : ℕ, term x (m + n) c) = _
  by_cases h : n ≤ c.1.1
  · rw [ite_eq_left h, j_apply]
    have he : ∀ m : ℕ, m ≠ c.1.1 - n → term x (m + n) c = 0 := by
      intro m hm
      exact term_apply_of_ne_level x (m + n) c (by omega)
    rw [tsum_eq_single (c.1.1 - n) he]
    rw [Nat.sub_add_cancel h]
  · rw [ite_eq_right h]
    calc
      (∑' m : ℕ, term x (m + n) c) = ∑' m : ℕ, (0 : ℝ) :=
        tsum_congr fun m => term_apply_of_ne_level x (m + n) c (by omega)
      _ = 0 := tsum_zero

end NoUniversalFSigma.Proof.Branch
