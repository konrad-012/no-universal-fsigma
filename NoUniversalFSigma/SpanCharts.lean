module

public import Mathlib

@[expose] public section

/-! # Closed charts for finite algebraic spans

The tail parameters need not lie in compact sets. Continuous recovery of each coefficient and
of each scaled tail controls them in a convergent sequence of sums. A positive lower bound on
the absolute coefficients permits division at the limit.
-/

open Set Filter
open scoped Topology

namespace NoUniversalFSigma.Proof

variable {S E : Type*} [Fintype S] [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- A finite sum chart with bounded nonzero coefficients and prescribed closed tail sets. -/
def finiteSpanChart (v : S → E) (C : S → Set E) (lower upper : ℝ) : Set E :=
  {b | ∃ a : S → ℝ, ∃ t : S → E,
    (∀ s, lower ≤ |a s| ∧ |a s| ≤ upper) ∧
    (∀ s, t s ∈ C s) ∧ b = ∑ s, a s • (v s + t s)}

/-- A finite sum chart is closed when its coefficients and scaled tails can be recovered
continuously from the sum. The tail sets themselves need not be bounded. -/
theorem isClosed_finiteSpanChart
    (v : S → E) (C : S → Set E) (lower upper : ℝ) (hlower : 0 < lower)
    (hC : ∀ s, IsClosed (C s))
    (coeff : S → E →L[ℝ] ℝ) (proj : S → E →L[ℝ] E)
    (hcoeff : ∀ (a : S → ℝ) (t : S → E), (∀ s, t s ∈ C s) →
      ∀ s, coeff s (∑ u, a u • (v u + t u)) = a s)
    (hproj : ∀ (a : S → ℝ) (t : S → E), (∀ s, t s ∈ C s) →
      ∀ s, proj s (∑ u, a u • (v u + t u)) = a s • t s) :
    IsClosed (finiteSpanChart v C lower upper) := by
  refine IsSeqClosed.isClosed fun z b hz hlim => ?_
  choose a t ha ht heq using hz
  have hcoeff_n (n : ℕ) (s : S) : coeff s (z n) = a n s := by
    rw [heq n]
    exact hcoeff (a n) (t n) (ht n) s
  have hproj_n (n : ℕ) (s : S) : proj s (z n) = a n s • t n s := by
    rw [heq n]
    exact hproj (a n) (t n) (ht n) s
  have haLim (s : S) : Tendsto (fun n => a n s) atTop (𝓝 (coeff s b)) := by
    simpa only [Function.comp_def, hcoeff_n] using ((coeff s).continuous.tendsto b).comp hlim
  have hbound (s : S) : lower ≤ |coeff s b| ∧ |coeff s b| ≤ upper :=
    isClosed_Icc.mem_of_tendsto ((haLim s).abs) (Eventually.of_forall fun n => ha n s)
  have hnonzero (s : S) : coeff s b ≠ 0 :=
    abs_pos.mp (hlower.trans_le (hbound s).1)
  have hnonzero_n (n : ℕ) (s : S) : a n s ≠ 0 :=
    abs_pos.mp (hlower.trans_le (ha n s).1)
  let tail : S → E := fun s => (coeff s b)⁻¹ • proj s b
  have htail_n (n : ℕ) (s : S) : t n s = (a n s)⁻¹ • proj s (z n) := by
    rw [hproj_n n s, smul_smul, inv_mul_cancel₀ (hnonzero_n n s), one_smul]
  have htLim (s : S) : Tendsto (fun n => t n s) atTop (𝓝 (tail s)) := by
    have h := ((haLim s).inv₀ (hnonzero s)).smul (((proj s).continuous.tendsto b).comp hlim)
    simpa only [Function.comp_def, ← htail_n] using h
  have htail (s : S) : tail s ∈ C s :=
    (hC s).mem_of_tendsto (htLim s) (Eventually.of_forall fun n => ht n s)
  have hsumLim : Tendsto (fun n => ∑ s, a n s • (v s + t n s)) atTop
      (𝓝 (∑ s, coeff s b • (v s + tail s))) :=
    tendsto_finsetSum Finset.univ fun s _ =>
      (haLim s).smul (tendsto_const_nhds.add (htLim s))
  have hlim' : Tendsto z atTop (𝓝 (∑ s, coeff s b • (v s + tail s))) := by
    simpa only [← heq] using hsumLim
  exact ⟨fun s => coeff s b, tail, hbound, htail, tendsto_nhds_unique hlim hlim'⟩

end NoUniversalFSigma.Proof
