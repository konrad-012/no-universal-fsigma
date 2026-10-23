module

public import NoUniversalFSigma.Admissible

@[expose] public section

/-! Countably many normalized finite-coordinate features separate any finite family of tails. -/

namespace NoUniversalFSigma.Proof

open Set Topology TopologicalSpace
open scoped lp

/-- A locally constant function on a separable space has countable range. -/
theorem countable_range_of_isLocallyConstant {P T : Type*}
    [TopologicalSpace P] [SeparableSpace P] {f : P → T} (hf : IsLocallyConstant f) :
    (range f).Countable := by
  obtain ⟨D, hD, hdense⟩ := TopologicalSpace.exists_countable_dense P
  apply (hD.image f).mono
  rintro y ⟨p, rfl⟩
  obtain ⟨x, hxD, hx⟩ := hdense.exists_mem_open (hf.isOpen_fiber (f p)) ⟨p, rfl⟩
  exact ⟨x, hxD, hx⟩

theorem hilbertFinsuppFunctional_add {I : Type*} (a b : I →₀ ℝ) (x : ℓ²(I, ℝ)) :
    hilbertFinsuppFunctional (a + b) x =
      hilbertFinsuppFunctional a x + hilbertFinsuppFunctional b x := by
  classical
  simp only [hilbertFinsuppFunctional_apply]
  change (a + b).sum (fun i r => r * x i) =
    a.sum (fun i r => r * x i) + b.sum (fun i r => r * x i)
  apply Finsupp.sum_add_index
  · intros
    ring
  · intros
    ring

theorem hilbertFinsuppFunctional_smul {I : Type*} (a : I →₀ ℝ) (c : ℝ) (x : ℓ²(I, ℝ)) :
    hilbertFinsuppFunctional (c • a) x = c * hilbertFinsuppFunctional a x := by
  classical
  simp only [hilbertFinsuppFunctional_apply]
  change (c • a).sum (fun i r => r * x i) = c * a.sum (fun i r => r * x i)
  rw [Finsupp.sum_smul_index (fun _ => zero_mul _)]
  simp only [mul_assoc, Finsupp.sum, Finset.mul_sum]

namespace AdmissibleFamily

noncomputable def featureValue (A : AdmissibleFamily) (n : ℕ) (p : A.Param) : ℝ :=
  hilbertFinsuppFunctional (A.features n) (A.j p)

theorem featureValue_locallyConstant (A : AdmissibleFamily) (n : ℕ) :
    IsLocallyConstant (A.featureValue n) := A.features_locallyConstant n

theorem featureValue_countable (A : AdmissibleFamily) (n : ℕ) :
    (range (A.featureValue n)).Countable :=
  countable_range_of_isLocallyConstant (A.featureValue_locallyConstant n)

/-- The range is countable even though the functionals themselves have real coefficients. -/
instance featureRangeCountable (A : AdmissibleFamily) (n : ℕ) :
    Countable (range (A.featureValue n)) := (A.featureValue_countable n).to_subtype

/-- One constant feature, or a feature normalized at two distinct values in its range. -/
def NormalizedFeature (A : AdmissibleFamily) :=
  Unit ⊕ (Σ n : ℕ,
    {p : range (A.featureValue n) × range (A.featureValue n) // p.1 ≠ p.2})

instance normalizedFeatureCountable (A : AdmissibleFamily) : Countable A.NormalizedFeature := by
  unfold NormalizedFeature
  infer_instance

/-- Normalization uses the mass-one functional to remain linear in the ambient space. -/
noncomputable def normalizedFunctional (A : AdmissibleFamily) :
    A.NormalizedFeature → (A.Coord →₀ ℝ)
  | .inl _ => A.mass
  | .inr ⟨n, ⟨⟨b, c⟩, _⟩⟩ =>
    (c.val - b.val)⁻¹ • (A.features n + (-b.val) • A.mass)

theorem normalizedFunctional_apply_atom (A : AdmissibleFamily) (n : ℕ)
    (b c : range (A.featureValue n)) (hbc : b ≠ c) (p : A.Param) :
    hilbertFinsuppFunctional
      (A.normalizedFunctional (.inr ⟨n, ⟨(b, c), hbc⟩⟩)) (A.j p) =
      (A.featureValue n p - b.val) / (c.val - b.val) := by
  rw [normalizedFunctional, hilbertFinsuppFunctional_smul, hilbertFinsuppFunctional_add,
    hilbertFinsuppFunctional_smul, A.mass_one]
  simp only [featureValue, mul_one, sub_eq_add_neg, div_eq_mul_inv]
  ring

theorem normalizedFunctional_locallyConstant (A : AdmissibleFamily)
    (a : A.NormalizedFeature) :
    IsLocallyConstant (hilbertFinsuppFunctional (A.normalizedFunctional a) ∘ A.j) := by
  cases a with
  | inl u =>
    convert IsLocallyConstant.const (1 : ℝ) using 1
    funext p
    exact A.mass_one p
  | inr a =>
    obtain ⟨n, ⟨⟨b, c⟩, hbc⟩⟩ := a
    have h := (A.featureValue_locallyConstant n).comp
      (fun x : ℝ => (x - b.val) / (c.val - b.val))
    convert h using 1
    funext p
    exact A.normalizedFunctional_apply_atom n b c hbc p

/-- Any two distinct parameters admit a normalized feature with values one and zero. -/
theorem exists_normalizedFeature (A : AdmissibleFamily) {p q : A.Param} (hpq : p ≠ q) :
    ∃ a : A.NormalizedFeature,
      hilbertFinsuppFunctional (A.normalizedFunctional a) (A.j p) = 1 ∧
      hilbertFinsuppFunctional (A.normalizedFunctional a) (A.j q) = 0 := by
  obtain ⟨n, hn⟩ := A.features_separate p q hpq
  let b : range (A.featureValue n) := ⟨A.featureValue n q, mem_range_self q⟩
  let c : range (A.featureValue n) := ⟨A.featureValue n p, mem_range_self p⟩
  have hbc : b ≠ c := by
    intro h
    exact hn (congrArg Subtype.val h).symm
  refine ⟨.inr ⟨n, ⟨(b, c), hbc⟩⟩, ?_, ?_⟩
  · rw [normalizedFunctional_apply_atom]
    exact div_self (sub_ne_zero.mpr hn)
  · rw [normalizedFunctional_apply_atom]
    simp only [b, sub_self, zero_div]

end AdmissibleFamily

end NoUniversalFSigma.Proof
