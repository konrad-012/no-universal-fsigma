module

public import NoUniversalFSigma.TensorCoordinates

@[expose] public section

/-! Coordinate inclusions and projections for Hilbert direct sums. -/

noncomputable section

open Set
open scoped lp ENNReal

namespace NoUniversalFSigma.Proof

attribute [local instance] Classical.propDecidable

variable {S : Type} {D : S → Type}

def sigmaCoordinate (s : S) (x : ℓ²(D s, ℝ)) (c : Σ s, D s) : ℝ :=
  if h : c.1 = s then x (h ▸ c.2) else 0

@[simp]
lemma sigmaCoordinate_mk (s : S) (x : ℓ²(D s, ℝ)) (c : D s) :
    sigmaCoordinate s x ⟨s, c⟩ = x c := by simp [sigmaCoordinate]

lemma sigmaCoordinate_other (s t : S) (x : ℓ²(D s, ℝ)) (c : D t) (h : t ≠ s) :
    sigmaCoordinate s x ⟨t, c⟩ = 0 := by simp [sigmaCoordinate, h]

lemma summable_sq_sigmaCoordinate (s : S) (x : ℓ²(D s, ℝ)) :
    Summable fun c => ‖sigmaCoordinate s x c‖ ^ 2 := by
  apply (summable_sigma_of_nonneg (fun _ => sq_nonneg _)).2
  constructor
  · intro t
    by_cases h : t = s
    · subst t
      simpa using hilbert_summable_sq x
    · simp only [sigmaCoordinate_other s t x _ h, norm_zero, ne_eq,
        OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow]
      exact summable_zero
  · have he : (fun t => ∑' c : D t, ‖sigmaCoordinate s x ⟨t, c⟩‖ ^ 2) =
        fun t => if t = s then ‖x‖ ^ 2 else 0 := by
      funext t
      split_ifs with h
      · subst t
        simpa using (hilbert_norm_sq x).symm
      · simp [sigmaCoordinate_other s t x _ h]
    rw [he]
    exact summable_of_hasFiniteSupport (by
      apply (Set.finite_singleton s).subset
      intro t ht
      by_contra h
      have hts : t ≠ s := fun he => h (Set.mem_singleton_iff.mpr he)
      exact (Function.mem_support.mp ht) (ite_eq_right hts))

def hilbertSigmaInclude (s : S) : ℓ²(D s, ℝ) →L[ℝ] ℓ²((Σ s, D s), ℝ) :=
  LinearMap.mkContinuous
    { toFun := fun x => ⟨sigmaCoordinate s x,
        memℓp_gen (by simpa using summable_sq_sigmaCoordinate s x)⟩
      map_add' := by
        intro x y
        apply lp.ext
        funext c
        change sigmaCoordinate s (x + y) c = sigmaCoordinate s x c + sigmaCoordinate s y c
        simp only [sigmaCoordinate]
        split_ifs <;> simp
      map_smul' := by
        intro r x
        apply lp.ext
        funext c
        change sigmaCoordinate s (r • x) c = r * sigmaCoordinate s x c
        simp only [sigmaCoordinate]
        split_ifs <;> simp }
    1 (by
      intro x
      rw [one_mul]
      apply le_of_sq_le_sq _ (norm_nonneg x)
      rw [hilbert_norm_sq]
      change (∑' c, ‖sigmaCoordinate s x c‖ ^ 2) ≤ _
      rw [(summable_sq_sigmaCoordinate s x).tsum_sigma']
      · rw [tsum_eq_single s]
        · simpa using (hilbert_norm_sq x).symm.le
        · intro t ht
          simp [sigmaCoordinate_other s t x _ ht]
      · intro t
        by_cases h : t = s
        · subst t; simpa using hilbert_summable_sq x
        · simp [sigmaCoordinate_other s t x _ h])

@[simp]
lemma hilbertSigmaInclude_apply (s : S) (x : ℓ²(D s, ℝ)) (c : Σ s, D s) :
    hilbertSigmaInclude s x c = sigmaCoordinate s x c := rfl

lemma norm_hilbertSigmaInclude (s : S) (x : ℓ²(D s, ℝ)) :
    ‖hilbertSigmaInclude s x‖ = ‖x‖ := by
  have he : ‖hilbertSigmaInclude s x‖ ^ 2 = ‖x‖ ^ 2 := by
    rw [hilbert_norm_sq]
    change (∑' c, ‖sigmaCoordinate s x c‖ ^ 2) = _
    rw [(summable_sq_sigmaCoordinate s x).tsum_sigma']
    · rw [tsum_eq_single s]
      · simpa using (hilbert_norm_sq x).symm
      · intro t ht
        simp [sigmaCoordinate_other s t x _ ht]
    · intro t
      by_cases h : t = s
      · subst t; simpa using hilbert_summable_sq x
      · simp [sigmaCoordinate_other s t x _ h]
  nlinarith [norm_nonneg (hilbertSigmaInclude s x), norm_nonneg x]

def hilbertSigmaProject (s : S) : ℓ²((Σ s, D s), ℝ) →L[ℝ] ℓ²(D s, ℝ) :=
  hilbertRestrict ⟨Sigma.mk s, fun _ _ h => eq_of_heq (Sigma.mk.inj_iff.mp h).2⟩

@[simp]
lemma hilbertSigmaProject_apply (s : S) (x : ℓ²((Σ s, D s), ℝ)) (c : D s) :
    hilbertSigmaProject s x c = x ⟨s, c⟩ := rfl

@[simp]
lemma hilbertSigmaProject_include (s : S) (x : ℓ²(D s, ℝ)) :
    hilbertSigmaProject s (hilbertSigmaInclude s x) = x := by
  ext c
  simp

lemma hilbertSigmaProject_include_other (s t : S) (x : ℓ²(D t, ℝ)) (h : s ≠ t) :
    hilbertSigmaProject s (hilbertSigmaInclude t x) = 0 := by
  ext c
  exact sigmaCoordinate_other t s x c h

lemma hilbertSigmaProject_tsum (x : ∀ s, ℓ²(D s, ℝ))
    (hx : Summable fun s => ‖x s‖) (t : S) :
    hilbertSigmaProject t (∑' s, hilbertSigmaInclude s (x s)) = x t := by
  have hs : Summable fun s => hilbertSigmaInclude s (x s) := by
    apply Summable.of_norm
    simpa only [norm_hilbertSigmaInclude] using hx
  rw [(hilbertSigmaProject t).map_tsum hs, tsum_eq_single t]
  · exact hilbertSigmaProject_include _ _
  · intro s hs
    exact hilbertSigmaProject_include_other t s (x s) (Ne.symm hs)

end NoUniversalFSigma.Proof
