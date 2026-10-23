module

public import Mathlib

@[expose] public section

/-! # Countable-coordinate real Hilbert spaces

The norm topology on real `ℓ²` is separable when the coordinate set is countable.  We use its
Borel sigma algebra explicitly, rather than inheriting a measurable structure from a space of
all coordinate functions.
-/

open Set Filter TopologicalSpace
open scoped lp ENNReal

namespace NoUniversalFSigma.Proof

attribute [local instance] Classical.propDecidable

/-- The finite linear combinations of coordinate unit vectors are dense in real `ℓ²`. -/
lemma dense_span_single (I : Type*) :
    Dense (Submodule.span ℝ (range fun i : I => lp.single (E := fun _ : I => ℝ) 2 i 1) :
      Set ℓ²(I, ℝ)) := by
  classical
  rw [dense_iff_closure_eq]
  apply eq_univ_of_forall
  intro x
  refine mem_closure_of_tendsto
    (lp.hasSum_single (by norm_num : (2 : ℝ≥0∞) ≠ ⊤) x) (Eventually.of_forall ?_)
  intro s
  apply Submodule.sum_mem
  intro i _
  have heq : lp.single (E := fun _ : I => ℝ) 2 i (x i) =
      x i • lp.single (E := fun _ : I => ℝ) 2 i 1 := by
    rw [← lp.single_smul]
    simp
  rw [heq]
  exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)

/-- Countably many coordinates give a separable real Hilbert space. -/
instance hilbertSeparableSpace (I : Type*) [Countable I] : SeparableSpace ℓ²(I, ℝ) := by
  apply isSeparable_univ_iff.mp
  rw [← (dense_span_single I).closure_eq]
  exact (countable_range fun i : I => lp.single (E := fun _ : I => ℝ) 2 i 1).isSeparable.span.closure

/-- The norm topology on countable-coordinate real `ℓ²` is second countable. -/
instance hilbertSecondCountableTopology (I : Type*) [Countable I] :
    SecondCountableTopology ℓ²(I, ℝ) := inferInstance

/-- Completeness and second countability make countable-coordinate real `ℓ²` Polish. -/
instance hilbertPolishSpace (I : Type*) [Countable I] : PolishSpace ℓ²(I, ℝ) := ⟨⟩

/-- Real `ℓ²` carries the Borel sigma algebra of its norm topology. -/
noncomputable instance hilbertMeasurableSpace (I : Type*) : MeasurableSpace ℓ²(I, ℝ) := borel _

instance hilbertBorelSpace (I : Type*) : BorelSpace ℓ²(I, ℝ) := ⟨rfl⟩

/-- Relabelling Hilbert coordinates along a bijection preserves the linear and metric structures. -/
noncomputable def hilbertReindex {I J : Type*} (e : I ≃ J) : ℓ²(I, ℝ) ≃ₗᵢ[ℝ] ℓ²(J, ℝ) where
  toFun x := ⟨fun j => x (e.symm j), memℓp_gen
    (e.symm.summable_iff.mpr ((lp.memℓp x).summable (by norm_num)))⟩
  invFun y := ⟨fun i => y (e i), memℓp_gen
    (e.summable_iff.mpr ((lp.memℓp y).summable (by norm_num)))⟩
  left_inv x := by ext i; simp
  right_inv y := by ext j; simp
  map_add' _x _y := by ext j; rfl
  map_smul' _r _x := by ext j; rfl
  norm_map' x := by
    rw [lp.norm_eq_tsum_rpow (by norm_num), lp.norm_eq_tsum_rpow (by norm_num)]
    congr 1
    exact e.symm.tsum_eq (fun i : I => ‖x i‖ ^ (2 : ℝ≥0∞).toReal)

@[simp]
lemma hilbertReindex_apply {I J : Type*} (e : I ≃ J) (x : ℓ²(I, ℝ)) (j : J) :
    hilbertReindex e x j = x (e.symm j) := rfl

@[simp]
lemma hilbertReindex_symm_apply {I J : Type*} (e : I ≃ J) (y : ℓ²(J, ℝ)) (i : I) :
    (hilbertReindex e).symm y i = y (e i) := rfl

/-- Setting every coordinate outside a chosen set to zero, as a continuous linear operator. -/
noncomputable def hilbertMask {I : Type*} (S : Set I) : ℓ²(I, ℝ) →L[ℝ] ℓ²(I, ℝ) :=
  LinearMap.mkContinuous
    { toFun := fun x => ⟨fun i => if i ∈ S then x i else 0,
        (lp.memℓp x).norm.mono (fun i => by split_ifs <;> simp)⟩
      map_add' := by
        intro x y
        ext i
        change (if i ∈ S then x i + y i else 0) =
          (if i ∈ S then x i else 0) + (if i ∈ S then y i else 0)
        split_ifs <;> simp
      map_smul' := by
        intro r x
        ext i
        change (if i ∈ S then r • x i else 0) = r • (if i ∈ S then x i else 0)
        split_ifs <;> simp }
    1 (by
      intro x
      rw [one_mul]
      apply lp.norm_mono (by norm_num)
      intro i
      change ‖if i ∈ S then x i else 0‖ ≤ ‖x i‖
      split_ifs <;> simp)

@[simp]
lemma hilbertMask_apply {I : Type*} (S : Set I) (x : ℓ²(I, ℝ)) (i : I) :
    hilbertMask S x i = if i ∈ S then x i else 0 := rfl

lemma norm_hilbertMask_le {I : Type*} (S : Set I) (x : ℓ²(I, ℝ)) :
    ‖hilbertMask S x‖ ≤ ‖x‖ := by
  apply lp.norm_mono (by norm_num)
  intro i
  rw [hilbertMask_apply]
  split_ifs <;> simp

lemma hilbertMask_opNorm_le_one {I : Type*} (S : Set I) : ‖hilbertMask S‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by norm_num)
  intro x
  simpa using norm_hilbertMask_le S x

@[simp]
lemma hilbertMask_idempotent {I : Type*} (S : Set I) (x : ℓ²(I, ℝ)) :
    hilbertMask S (hilbertMask S x) = hilbertMask S x := by
  ext i
  simp only [hilbertMask_apply]
  split_ifs <;> rfl

/-- A finitely supported linear combination of coordinate evaluations. -/
noncomputable def hilbertFinsuppFunctional {I : Type*} (a : I →₀ ℝ) : ℓ²(I, ℝ) →L[ℝ] ℝ :=
  ∑ i ∈ a.support, a i • lp.evalCLM ℝ (fun _ : I => ℝ) 2 i

@[simp]
lemma hilbertFinsuppFunctional_apply {I : Type*} (a : I →₀ ℝ) (x : ℓ²(I, ℝ)) :
    hilbertFinsuppFunctional a x = ∑ i ∈ a.support, a i * x i := by
  simp only [hilbertFinsuppFunctional, sum_apply, smul_apply, smul_eq_mul]
  rfl

@[simp]
lemma hilbertFinsuppFunctional_single {I : Type*} (a : I →₀ ℝ) (i : I) (r : ℝ) :
    hilbertFinsuppFunctional a (lp.single (E := fun _ : I => ℝ) 2 i r) = a i * r := by
  rw [hilbertFinsuppFunctional_apply]
  simp only [lp.single_apply, Pi.single_apply, mul_ite, mul_zero]
  rw [Finset.sum_ite_eq']
  split_ifs with hi
  · rfl
  · rw [Finsupp.notMem_support_iff.mp hi, zero_mul]

end NoUniversalFSigma.Proof
