module

public import NoUniversalFSigma.Admissible
public import NoUniversalFSigma.FinitePi
public import NoUniversalFSigma.HilbertSigma

@[expose] public section

/-! The countable tensor packet family, in finite-subset Hilbert coordinates. -/

noncomputable section

open Set Filter Topology
open scoped lp ENNReal

namespace NoUniversalFSigma.Proof.Packet

attribute [local instance] Classical.propDecidable

variable (A : ℕ → AdmissibleFamily)

abbrev Param := ∀ n, (A n).Param

abbrev BlockCoord (F : Finset ℕ) := ∀ n : F, (A n.val).Coord

abbrev Coord := Σ F : Finset ℕ, BlockCoord A F

abbrev Space := ℓ²(Coord A, ℝ)

def beta (n : ℕ) : ℝ := (1 / 2 : ℝ) ^ (n + 1) / (1 + (A n).bound)

lemma beta_pos (n : ℕ) : 0 < beta A n := by
  exact div_pos (by positivity) (by linarith [(A n).bound_nonneg])

lemma beta_ne_zero (n : ℕ) : beta A n ≠ 0 := (beta_pos A n).ne'

lemma beta_le (n : ℕ) : beta A n ≤ (1 / 2 : ℝ) ^ (n + 1) := by
  rw [beta, div_le_iff₀ (by linarith [(A n).bound_nonneg])]
  have h : 0 ≤ (1 / 2 : ℝ) ^ (n + 1) := by positivity
  nlinarith [(A n).bound_nonneg]

def block (F : Finset ℕ) (q : Param A) : ℓ²(BlockCoord A F, ℝ) :=
  hilbertPi F (fun n => (A n.val).Coord) (fun n => beta A n.val • (A n.val).j (q n.val))

@[simp]
lemma block_apply (F : Finset ℕ) (q : Param A) (c : BlockCoord A F) :
    block A F q c = ∏ n : F, beta A n.val * (A n.val).j (q n.val) (c n) := rfl

def majorant (F : Finset ℕ) : ℝ := ∏ n ∈ F, (1 / 2 : ℝ) ^ (n + 1)

lemma majorant_nonneg (F : Finset ℕ) : 0 ≤ majorant F := by
  exact Finset.prod_nonneg fun _ _ => by positivity

lemma summable_majorant : Summable majorant := by
  apply summable_finsetProd_of_summable_nonneg (fun _ => by positivity)
  simpa only [pow_succ] using
    (summable_geometric_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2)
      (by norm_num : (1 / 2 : ℝ) < 1)).mul_right (1 / 2)

lemma norm_scaled_atom_le (n : ℕ) (q : Param A) :
    ‖beta A n • (A n).j (q n)‖ ≤ (1 / 2 : ℝ) ^ (n + 1) := by
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos (beta_pos A n)]
  calc
    beta A n * ‖(A n).j (q n)‖ ≤ beta A n * (A n).bound :=
      mul_le_mul_of_nonneg_left ((A n).norm_le _) (beta_pos A n).le
    _ ≤ (1 / 2 : ℝ) ^ (n + 1) := by
      rw [beta, div_mul_eq_mul_div, div_le_iff₀ (by linarith [(A n).bound_nonneg])]
      have h : 0 ≤ (1 / 2 : ℝ) ^ (n + 1) := by positivity
      nlinarith

lemma norm_block_le (F : Finset ℕ) (q : Param A) : ‖block A F q‖ ≤ majorant F := by
  rw [block, norm_hilbertPi]
  calc
    (∏ n : F, ‖beta A n.val • (A n.val).j (q n.val)‖) ≤
        ∏ n : F, (1 / 2 : ℝ) ^ (n.val + 1) :=
      Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _) (fun n _ => norm_scaled_atom_le A n.val q)
    _ = majorant F := Finset.prod_coe_sort F (fun n => (1 / 2 : ℝ) ^ (n + 1))

def term (F : Finset ℕ) (q : Param A) : Space A := hilbertSigmaInclude F (block A F q)

lemma norm_term_le (F : Finset ℕ) (q : Param A) : ‖term A F q‖ ≤ majorant F := by
  rw [term, norm_hilbertSigmaInclude]
  exact norm_block_le A F q

lemma summable_norm_term (q : Param A) : Summable fun F => ‖term A F q‖ :=
  Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun F => norm_term_le A F q)
    summable_majorant

lemma summable_term (q : Param A) : Summable fun F => term A F q :=
  (summable_norm_term A q).of_norm

def j (q : Param A) : Space A := ∑' F, term A F q

lemma norm_j_le (q : Param A) : ‖j A q‖ ≤ ∑' F, majorant F := by
  exact (norm_tsum_le_tsum_norm (summable_norm_term A q)).trans
    ((summable_norm_term A q).tsum_le_tsum (fun F => norm_term_le A F q) summable_majorant)

lemma j_apply (q : Param A) (c : Coord A) : j A q c = block A c.1 q c.2 := by
  change (lp.evalCLM ℝ (fun _ : Coord A => ℝ) 2 c) (∑' F, term A F q) = _
  rw [(lp.evalCLM ℝ (fun _ : Coord A => ℝ) 2 c).map_tsum (summable_term A q)]
  change (∑' F, sigmaCoordinate F (block A F q) c) = _
  rw [tsum_eq_single c.1]
  · rcases c with ⟨F, c⟩
    exact sigmaCoordinate_mk _ _ _
  · intro F hF
    exact sigmaCoordinate_other F c.1 (block A F q) c.2 (Ne.symm hF)

def emptyCoord : Coord A := ⟨∅, fun n => False.elim (Finset.notMem_empty n.val n.property)⟩

@[simp]
lemma j_empty (q : Param A) : j A q (emptyCoord A) = 1 := by
  rw [j_apply, block_apply]
  change (∏ n : (∅ : Finset ℕ), _) = 1
  simp

def singletonBlockCoord (n : ℕ) (c : (A n).Coord) : BlockCoord A {n} := fun m =>
  (Finset.mem_singleton.mp m.property).symm ▸ c

def singletonCoord (n : ℕ) (c : (A n).Coord) : Coord A :=
  ⟨{n}, singletonBlockCoord A n c⟩

lemma singletonCoord_injective (n : ℕ) : Function.Injective (singletonCoord A n) := by
  intro c d h
  have he := eq_of_heq (Sigma.mk.inj_iff.mp h).2
  have hf := congrFun he (⟨n, Finset.mem_singleton_self n⟩ : ({n} : Finset ℕ))
  simpa [singletonBlockCoord] using hf

@[simp]
lemma j_singleton (q : Param A) (n : ℕ) (c : (A n).Coord) :
    j A q (singletonCoord A n c) = beta A n * (A n).j (q n) c := by
  rw [j_apply, block_apply]
  change (∏ m : ({n} : Finset ℕ),
    beta A m.val * (A m.val).j (q m.val) (singletonBlockCoord A n c m)) = _
  rw [Fintype.prod_eq_single (⟨n, Finset.mem_singleton_self n⟩ : ({n} : Finset ℕ))]
  · simp [singletonBlockCoord]
  · intro m hm
    exact (hm (Subtype.ext (Finset.mem_singleton.mp m.property))).elim

/-- The original `n`-th Hilbert vector is recovered from the singleton packet. -/
def recover (n : ℕ) : Space A →L[ℝ] (A n).Space :=
  (beta A n)⁻¹ • hilbertRestrict ⟨singletonCoord A n, singletonCoord_injective A n⟩

@[simp]
lemma recover_j (q : Param A) (n : ℕ) : recover A n (j A q) = (A n).j (q n) := by
  ext c
  change (beta A n)⁻¹ * j A q (singletonCoord A n c) = _
  rw [j_singleton, ← mul_assoc, inv_mul_cancel₀ (beta_ne_zero A n), one_mul]

def span : Submodule ℝ (Space A) := Submodule.span ℝ (range (j A))

lemma recover_mem_span (n : ℕ) {z : Space A} (hz : z ∈ span A) :
    recover A n z ∈ (A n).span := by
  induction hz using Submodule.span_induction with
  | mem z hz =>
    obtain ⟨q, rfl⟩ := hz
    rw [recover_j]
    exact (A n).j_mem_span _
  | zero => simp
  | add x y _ _ hx hy => simpa using (A n).span.add_mem hx hy
  | smul r x _ hx => simpa using (A n).span.smul_mem r hx

lemma j_injective : Function.Injective (j A) := by
  intro q r h
  funext n
  apply (A n).closedEmbedding.injective
  have he := congrArg (recover A n) h
  simpa using he

lemma project_j (q : Param A) (F : Finset ℕ) :
    hilbertSigmaProject F (j A q) = block A F q := by
  ext c
  exact j_apply A q ⟨F, c⟩

lemma continuous_block (F : Finset ℕ) : Continuous (block A F) := by
  apply (continuous_hilbertPi F (fun n => (A n.val).Coord)).comp
  apply continuous_pi
  intro n
  have h : Continuous fun q : Param A => (A n.val).j (q n.val) :=
    (A n.val).continuous_j.comp (continuous_apply n.val)
  exact h.const_smul (beta A n.val)

lemma continuous_j : Continuous (j A) := by
  apply continuous_tsum (fun F => (hilbertSigmaInclude F).continuous.comp (continuous_block A F))
    summable_majorant
  intro F q
  exact norm_term_le A F q

lemma exists_tendsto_of_tendsto_j (u : ℕ → Param A) {z : Space A}
    (hz : Tendsto (fun m => j A (u m)) atTop (𝓝 z)) :
    ∃ q : Param A, Tendsto u atTop (𝓝 q) := by
  have hrec (n : ℕ) : Tendsto (fun m => (A n).j (u m n)) atTop (𝓝 (recover A n z)) := by
    simpa only [Function.comp_def, recover_j] using ((recover A n).continuous.tendsto z).comp hz
  have hmem (n : ℕ) : recover A n z ∈ range (A n).j :=
    (A n).closedEmbedding.isClosed_range.mem_of_tendsto (hrec n)
      (Eventually.of_forall fun m => mem_range_self (u m n))
  choose q hq using hmem
  refine ⟨q, tendsto_pi_nhds.2 fun n => ?_⟩
  apply (A n).closedEmbedding.tendsto_nhds_iff.2
  simpa only [Function.comp_def, hq] using hrec n

lemma isClosedMap_j : IsClosedMap (j A) := by
  intro C hC
  apply isSeqClosed_iff_isClosed.mp
  intro u z hu hz
  choose v hv hvj using hu
  have hvlim : Tendsto (fun m => j A (v m)) atTop (𝓝 z) := by simpa only [hvj] using hz
  obtain ⟨q, hq⟩ := exists_tendsto_of_tendsto_j A v hvlim
  refine ⟨q, hC.mem_of_tendsto hq (Eventually.of_forall hv), ?_⟩
  exact tendsto_nhds_unique ((continuous_j A).continuousAt.tendsto.comp hq) hvlim

theorem isClosedEmbedding_j : IsClosedEmbedding (j A) :=
  IsClosedEmbedding.of_continuous_injective_isClosedMap
    (continuous_j A) (j_injective A) (isClosedMap_j A)

/-- A feature of one factor, supported on its singleton packet coordinates. -/
def liftFeature (n : ℕ) (a : (A n).Coord →₀ ℝ) : Coord A →₀ ℝ :=
  a.embDomain ⟨singletonCoord A n, singletonCoord_injective A n⟩

lemma liftFeature_j (n : ℕ) (a : (A n).Coord →₀ ℝ) (q : Param A) :
    hilbertFinsuppFunctional (liftFeature A n a) (j A q) =
      beta A n * hilbertFinsuppFunctional a ((A n).j (q n)) := by
  simp only [hilbertFinsuppFunctional_apply, liftFeature, Finsupp.support_embDomain,
    Finset.sum_map]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro c _
  rw [Finsupp.embDomain_apply_self]
  change a c * j A q (singletonCoord A n c) = _
  rw [j_singleton]
  ring

def mass : Coord A →₀ ℝ := Finsupp.single (emptyCoord A) 1

lemma mass_one (q : Param A) : hilbertFinsuppFunctional (mass A) (j A q) = 1 := by
  simp [mass, hilbertFinsuppFunctional_apply]

def features (k : ℕ) : Coord A →₀ ℝ :=
  liftFeature A k.unpair.1 ((A k.unpair.1).features k.unpair.2)

lemma features_locallyConstant (k : ℕ) :
    IsLocallyConstant (hilbertFinsuppFunctional (features A k) ∘ j A) := by
  have h := ((A k.unpair.1).features_locallyConstant k.unpair.2).comp_continuous
    (continuous_apply k.unpair.1 : Continuous fun q : Param A => q k.unpair.1)
  have hm := h.comp (fun r : ℝ => beta A k.unpair.1 * r)
  simpa only [Function.comp_def, features, liftFeature_j] using hm

lemma features_separate (q r : Param A) (hqr : q ≠ r) :
    ∃ k, hilbertFinsuppFunctional (features A k) (j A q) ≠
      hilbertFinsuppFunctional (features A k) (j A r) := by
  obtain ⟨n, hn⟩ : ∃ n, q n ≠ r n := by
    by_contra h
    push Not at h
    exact hqr (funext h)
  obtain ⟨m, hm⟩ := (A n).features_separate _ _ hn
  refine ⟨Nat.pair n m, ?_⟩
  unfold features
  rw [Nat.unpair_pair]
  change hilbertFinsuppFunctional (liftFeature A n ((A n).features m)) (j A q) ≠ _
  rw [liftFeature_j, liftFeature_j]
  exact fun h => hm (mul_left_cancel₀ (beta_ne_zero A n) h)

end NoUniversalFSigma.Proof.Packet
