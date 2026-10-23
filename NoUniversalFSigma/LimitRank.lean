module

public import NoUniversalFSigma.Admissible
public import NoUniversalFSigma.Escape

@[expose] public section

/-! Escape ranks of countable product families, using linear coordinate insertions. -/

namespace NoUniversalFSigma.Proof

open Set Filter Topology
open scoped lp

section CoordinateTransfer

variable (A : ℕ → AdmissibleFamily)
variable {C : Type} [NormedAddCommGroup C] [NormedSpace ℝ C]
variable (J : (∀ n, (A n).Param) → C)

/-- A linear map that sends all atoms into another span also sends the algebraic span there. -/
theorem map_mem_span_of_atoms {P D : Type} [AddCommGroup D] [Module ℝ D]
    (j : P → D) (L : D →ₗ[ℝ] C) (hL : ∀ p, L (j p) ∈ Submodule.span ℝ (range J))
    {v : D} (hv : v ∈ Submodule.span ℝ (range j)) :
    L v ∈ Submodule.span ℝ (range J) := by
  have hle : Submodule.span ℝ (range j) ≤
      (Submodule.span ℝ (range J)).comap L := by
    apply Submodule.span_le.mpr
    rintro _ ⟨p, rfl⟩
    exact hL p
  exact hle hv

/-- Varying one parameter transfers the corresponding factor's whole escape remainder.
The insertion and recovery maps concern the ambient Hilbert spaces. -/
theorem coordinate_remainder_transfer (i : ℕ) (q : ∀ n, (A n).Param)
    (T : (A i).Space →L[ℝ] C) (π : C →L[ℝ] (A i).Space)
    (hT : ∀ t, T ((A i).j t) = J (Function.update q i t))
    (hπ : ∀ r, π (J r) = (A i).j (r i))
    (hπT : ∀ v, π (T v) = v) (α : Ordinal) :
    ∀ p ∈ escapeRemainder (A i).j (A i).span.toAddSubgroup α,
      (Function.update q i p.1, Function.update q i p.2) ∈
        escapeRemainder J (Submodule.span ℝ (range J)).toAddSubgroup α := by
  apply escapeRemainder_transfer (A i).j (A i).span.toAddSubgroup J
    (Submodule.span ℝ (range J)).toAddSubgroup
    (Function.update q i) (Function.update q i)
    (continuous_const.update i continuous_id) (continuous_const.update i continuous_id)
    T T.continuous
  · intro t u
    simp only [pairSum, ← hT, map_add]
  · intro v hv hmem
    have hle : Submodule.span ℝ (range J) ≤ (A i).span.comap π.toLinearMap := by
      apply Submodule.span_le.mpr
      rintro _ ⟨r, rfl⟩
      change π (J r) ∈ (A i).span
      rw [hπ]
      exact (A i).j_mem_span (r i)
    have hproj : π (T v) ∈ (A i).span :=
      hle ((Submodule.span ℝ (range J)).mem_toAddSubgroup.mp hmem)
    exact hv ((A i).span.mem_toAddSubgroup.mpr (by rwa [hπT] at hproj))

/-- A product family inherits each coordinate's diagonal rank. -/
theorem coordinate_diagonal_rank (i : ℕ)
    (T : (∀ n, (A n).Param) → (A i).Space →L[ℝ] C)
    (π : C →L[ℝ] (A i).Space)
    (hT : ∀ q t, T q ((A i).j t) = J (Function.update q i t))
    (hπ : ∀ r, π (J r) = (A i).j (r i))
    (hπT : ∀ q v, π (T q v) = v) (α : Ordinal)
    (hα : ∀ t, (t, t) ∈ escapeRemainder (A i).j (A i).span.toAddSubgroup α) :
    ∀ q, (q, q) ∈ escapeRemainder J (Submodule.span ℝ (range J)).toAddSubgroup α := by
  intro q
  have h := coordinate_remainder_transfer A J i q (T q) π (hT q) hπ (hπT q)
    α (q i, q i) (hα (q i))
  simpa only [Function.update_eq_self] using h

/-- Cofinal factor ranks give the full limit diagonal rank. -/
theorem cofinal_diagonal_rank (r : ℕ → Ordinal) (lambda : Ordinal)
    (hlambda : Order.IsSuccLimit lambda) (hr : ∀ β < lambda, ∃ i, β ≤ r i)
    (T : ∀ i, (∀ n, (A n).Param) → (A i).Space →L[ℝ] C)
    (π : ∀ i, C →L[ℝ] (A i).Space)
    (hT : ∀ i q t, T i q ((A i).j t) = J (Function.update q i t))
    (hπ : ∀ i q, π i (J q) = (A i).j (q i))
    (hπT : ∀ i q v, π i (T i q v) = v)
    (hα : ∀ i t, (t, t) ∈ escapeRemainder (A i).j (A i).span.toAddSubgroup (r i)) :
    ∀ q, (q, q) ∈ escapeRemainder J (Submodule.span ℝ (range J)).toAddSubgroup lambda := by
  intro q
  rw [escapeRemainder_limit J _ hlambda]
  apply mem_iInter.mpr
  intro β
  obtain ⟨i, hi⟩ := hr β.1 β.2
  exact escapeRemainder_antitone J _ hi
    (coordinate_diagonal_rank A J i (T i) (π i) (hT i) (hπ i) (hπT i) (r i) (hα i) q)

end CoordinateTransfer

end NoUniversalFSigma.Proof
