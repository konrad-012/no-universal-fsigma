module

public import Mathlib

@[expose] public section

/-! Closed charts for finite mixtures with product labels.

Continuous recovery of the vector coefficients and of each scaled label coordinate controls
convergent sequences of chart vectors. The labels need not range over compact sets.
-/

namespace NoUniversalFSigma.Proof

open Set Filter Topology

variable {S N E V : Type*} [Fintype S]
  [NormedAddCommGroup E]
  [NormedAddCommGroup V]
  {Q W : N → Type*} [∀ n, TopologicalSpace (Q n)]
  [∀ n, NormedAddCommGroup (W n)] [∀ n, NormedSpace ℝ (W n)]

/-- A finite sum with constrained vector coefficients and product labels. -/
def mixtureChart (mix : V → (∀ n, Q n) → E) (C : S → Set V)
    (pin : Set (S → ∀ n, Q n)) : Set E :=
  {z | ∃ v : S → V, ∃ q : S → ∀ n, Q n,
    (∀ c, v c ∈ C c) ∧ q ∈ pin ∧ z = ∑ c, mix (v c) (q c)}

/-- Coordinatewise closed embeddings suffice for closedness of a mixture chart.
Two disjoint witness packets in the countable tensor construction provide the recovery maps
appearing in this abstract statement. -/
theorem isClosed_mixtureChart
    (mix : V → (∀ n, Q n) → E) (hmix : Continuous (Function.uncurry mix))
    (C : S → Set V) (hC : ∀ c, IsClosed (C c))
    (pin : Set (S → ∀ n, Q n)) (hpin : IsClosed pin)
    (j : ∀ n, Q n → W n) (hj : ∀ n, IsClosedEmbedding (j n))
    (coeff : S → E → V) (hcoeff : ∀ c, Continuous (coeff c))
    (mass : S → V → ℝ) (hmass : ∀ c, Continuous (mass c))
    (hnonzero : ∀ c v, v ∈ C c → mass c v ≠ 0)
    (recover : ∀ _c : S, ∀ n, E → W n)
    (hrecover : ∀ c n, Continuous (recover c n))
    (hcoeff_sum : ∀ (v : S → V) (q : S → ∀ n, Q n), q ∈ pin →
      ∀ c, coeff c (∑ d, mix (v d) (q d)) = v c)
    (hrecover_sum : ∀ (v : S → V) (q : S → ∀ n, Q n), q ∈ pin →
      ∀ c n, recover c n (∑ d, mix (v d) (q d)) = mass c (v c) • j n (q c n)) :
    IsClosed (mixtureChart mix C pin) := by
  classical
  refine IsSeqClosed.isClosed fun z b hz hlim => ?_
  choose v q hv hq heq using hz
  have hcoeff_z (l : ℕ) (c : S) : coeff c (z l) = v l c := by
    rw [heq l]
    exact hcoeff_sum (v l) (q l) (hq l) c
  have hvlim (c : S) : Tendsto (fun l => v l c) atTop (𝓝 (coeff c b)) := by
    simpa only [Function.comp_def, hcoeff_z] using ((hcoeff c).tendsto b).comp hlim
  have hvc (c : S) : coeff c b ∈ C c :=
    (hC c).mem_of_tendsto (hvlim c) (Eventually.of_forall fun l => hv l c)
  have hmasslim (c : S) : Tendsto (fun l => mass c (v l c)) atTop
      (𝓝 (mass c (coeff c b))) := ((hmass c).tendsto _).comp (hvlim c)
  let w : ∀ c : S, ∀ n, W n := fun c n =>
    (mass c (coeff c b))⁻¹ • recover c n b
  have hjlim (c : S) (n : N) : Tendsto (fun l => j n (q l c n)) atTop (𝓝 (w c n)) := by
    have h := ((hmasslim c).inv₀ (hnonzero c _ (hvc c))).smul
      (((hrecover c n).tendsto b).comp hlim)
    convert h using 1
    funext l
    dsimp only [Function.comp_def]
    rw [heq l, hrecover_sum (v l) (q l) (hq l) c n, smul_smul,
      inv_mul_cancel₀ (hnonzero c _ (hv l c)), one_smul]
  have hw (c : S) (n : N) : w c n ∈ range (j n) :=
    (hj n).isClosed_range.mem_of_tendsto (hjlim c n)
      (Eventually.of_forall fun l => mem_range_self (q l c n))
  choose tail htail using hw
  have htail_lim (c : S) (n : N) : Tendsto (fun l => q l c n) atTop (𝓝 (tail c n)) := by
    apply (hj n).isEmbedding.isInducing.tendsto_nhds_iff.mpr
    simpa only [Function.comp_def, htail] using hjlim c n
  have hqlim : Tendsto q atTop (𝓝 tail) :=
    tendsto_pi_nhds.mpr fun c => tendsto_pi_nhds.mpr fun n => htail_lim c n
  have htail_pin : tail ∈ pin :=
    hpin.mem_of_tendsto hqlim (Eventually.of_forall hq)
  have hsumlim : Tendsto (fun l => ∑ c, mix (v l c) (q l c)) atTop
      (𝓝 (∑ c, mix (coeff c b) (tail c))) := by
    apply tendsto_finsetSum
    intro c _
    exact (hmix.tendsto _).comp ((hvlim c).prodMk_nhds
      (tendsto_pi_nhds.mpr fun n => htail_lim c n))
  have hzlim : Tendsto z atTop (𝓝 (∑ c, mix (coeff c b) (tail c))) := by
    simpa only [← heq] using hsumlim
  exact ⟨fun c => coeff c b, tail, hvc, htail_pin, tendsto_nhds_unique hlim hzlim⟩

end NoUniversalFSigma.Proof
