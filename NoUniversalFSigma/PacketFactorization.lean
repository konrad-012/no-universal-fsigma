module

public import NoUniversalFSigma.PacketCoordinates
public import NoUniversalFSigma.PacketSplit
public import NoUniversalFSigma.PacketGraph

@[expose] public section

/-! Finite packet cuts and the corresponding tensor mixtures. -/

noncomputable section

open Set Filter Topology
open scoped lp

namespace NoUniversalFSigma.Proof.Packet

variable (A : ℕ → AdmissibleFamily)

abbrev HeadCoord (B : Finset ℕ) := ∀ n : B, Option (A n.val).Coord

abbrev OutsideCoord (B : Finset ℕ) :=
  PacketSplit.Coord (fun n : {n // n ∉ B} => (A n.val).Coord)

abbrev HeadSpace (B : Finset ℕ) := ℓ²(HeadCoord A B, ℝ)

abbrev OutsideSpace (B : Finset ℕ) := ℓ²(OutsideCoord A B, ℝ)

abbrev TailParam (B : Finset ℕ) := ∀ n : {n // n ∉ B}, (A n.val).Param

abbrev HeadParam (B : Finset ℕ) := ∀ n : B, (A n.val).Param

def restrictHead (B : Finset ℕ) (q : Param A) : HeadParam A B := fun n => q n.val

def restrictParam (B : Finset ℕ) (q : Param A) : TailParam A B := fun n => q n.val

def fillParam (B : Finset ℕ) (q : TailParam A B) : Param A := fun n =>
  if h : n ∈ B then Classical.choice (A n).nonemptyParam else q ⟨n, h⟩

def combineParam (B : Finset ℕ) (p : HeadParam A B) (q : TailParam A B) : Param A := fun n =>
  if h : n ∈ B then p ⟨n, h⟩ else q ⟨n, h⟩

@[simp]
lemma restrictHead_combineParam (B : Finset ℕ) (p : HeadParam A B) (q : TailParam A B) :
    restrictHead A B (combineParam A B p q) = p := by
  funext n
  simp [restrictHead, combineParam, n.property]

@[simp]
lemma restrictParam_combineParam (B : Finset ℕ) (p : HeadParam A B) (q : TailParam A B) :
    restrictParam A B (combineParam A B p q) = q := by
  funext n
  simp [restrictParam, combineParam, n.property]

@[simp]
lemma combineParam_restrict (B : Finset ℕ) (q : Param A) :
    combineParam A B (restrictHead A B q) (restrictParam A B q) = q := by
  funext n
  simp only [combineParam, restrictHead, restrictParam]
  split_ifs <;> rfl

@[simp]
lemma fillParam_outside (B : Finset ℕ) (q : TailParam A B) (n : {n // n ∉ B}) :
    fillParam A B q n.val = q n := by simp [fillParam, n.property]

lemma continuous_fillParam (B : Finset ℕ) : Continuous (fillParam A B) := by
  apply continuous_pi
  intro n
  by_cases h : n ∈ B
  · simpa only [fillParam, h, dite_true] using
      (continuous_const : Continuous fun _ : TailParam A B => Classical.choice (A n).nonemptyParam)
  · simpa only [fillParam, h, dite_false] using
      (continuous_apply (⟨n, h⟩ : {n // n ∉ B}))

def split (B : Finset ℕ) :
    Space A ≃ₗᵢ[ℝ] ℓ²(HeadCoord A B × OutsideCoord A B, ℝ) :=
  PacketSplit.hilbertSplit (fun n => (A n).Coord) B

def emptyHead (B : Finset ℕ) : HeadCoord A B := fun _ => none

def oneFactor (n : ℕ) (t : (A n).Param) : ℓ²(Option (A n).Coord, ℝ) :=
  hilbertOptionGraph (A n).mass (beta A n) ((A n).j t)

@[simp]
lemma oneFactor_none (n : ℕ) (t : (A n).Param) : oneFactor A n t none = 1 := by
  rw [oneFactor, hilbertOptionGraph_none]
  exact (A n).mass_one t

@[simp]
lemma oneFactor_some (n : ℕ) (t : (A n).Param) (c : (A n).Coord) :
    oneFactor A n t (some c) = beta A n * (A n).j t c := rfl

def finitePacket (B : Finset ℕ) (p : HeadParam A B) : HeadSpace A B :=
  hilbertPi B (fun n => Option (A n.val).Coord) (fun n => oneFactor A n.val (p n))

lemma finitePacket_apply (B : Finset ℕ) (p : HeadParam A B) (c : HeadCoord A B) :
    finitePacket A B p c = ∏ n : B, Option.elim (c n) 1
      (fun d => beta A n.val * (A n.val).j (p n) d) := by
  rw [finitePacket, hilbertPi_apply]
  apply Finset.prod_congr rfl
  intro n _
  cases c n <;> simp

@[simp]
lemma finitePacket_emptyHead (B : Finset ℕ) (p : HeadParam A B) :
    finitePacket A B p (emptyHead A B) = 1 := by
  rw [finitePacket_apply]
  simp [emptyHead]

lemma continuous_finitePacket (B : Finset ℕ) : Continuous (finitePacket A B) := by
  apply (continuous_hilbertPi B (fun n => Option (A n.val).Coord)).comp
  apply continuous_pi
  intro n
  exact (hilbertOptionGraph (A n.val).mass (beta A n.val)).continuous.comp
    ((A n.val).continuous_j.comp (continuous_apply n))

lemma finitePacket_apply_choice (B : Finset ℕ) (q : Param A) (c : HeadCoord A B) :
    finitePacket A B (restrictHead A B q) c =
      ∏ n : B, PacketSplit.choiceValue (fun n => (A n).Coord)
        (fun n d => beta A n * (A n).j (q n) d) n.val (c n) := by
  rw [finitePacket_apply]
  apply Finset.prod_congr rfl
  intro n _
  cases c n <;> rfl

lemma split_j_apply (B : Finset ℕ) (q : Param A)
    (c : HeadCoord A B × OutsideCoord A B) :
    split A B (j A q) c = finitePacket A B (restrictHead A B q) c.1 *
      PacketSplit.coordProduct (fun n : {n // n ∉ B} => (A n.val).Coord)
        (fun n d => beta A n.val * (A n.val).j (q n.val) d) c.2 := by
  rw [finitePacket_apply_choice]
  change j A q ((PacketSplit.coordSplit (fun n => (A n).Coord) B).symm c) = _
  rw [j_apply, block_apply]
  exact (PacketSplit.coordProduct_split (fun n => (A n).Coord) B
    (fun n d => beta A n * (A n).j (q n) d)
    ((PacketSplit.coordSplit (fun n => (A n).Coord) B).symm c)).trans (by
      simp only [Equiv.apply_symm_apply])

/-- The outside row of a full packet. -/
def outsideJFull (B : Finset ℕ) (q : Param A) : OutsideSpace A B :=
  hilbertRow (emptyHead A B) (split A B (j A q))

/-- The outside packet is the row with no selected finite-head coordinates. -/
def outsideJ (B : Finset ℕ) (q : TailParam A B) : OutsideSpace A B :=
  outsideJFull A B (fillParam A B q)

lemma outsideJFull_apply (B : Finset ℕ) (q : Param A) (c : OutsideCoord A B) :
    outsideJFull A B q c =
      PacketSplit.coordProduct (fun n : {n // n ∉ B} => (A n.val).Coord)
        (fun n d => beta A n.val * (A n.val).j (q n.val) d) c := by
  change split A B (j A q) (emptyHead A B, c) = _
  rw [split_j_apply, finitePacket_emptyHead, one_mul]

lemma outsideJ_apply (B : Finset ℕ) (q : TailParam A B) (c : OutsideCoord A B) :
    outsideJ A B q c =
      PacketSplit.coordProduct (fun n : {n // n ∉ B} => (A n.val).Coord)
        (fun n d => beta A n.val * (A n.val).j (q n) d) c := by
  rw [outsideJ, outsideJFull_apply]
  simp only [PacketSplit.coordProduct, fillParam_outside]

def emptyOutside (B : Finset ℕ) : OutsideCoord A B :=
  ⟨∅, fun n => False.elim (Finset.notMem_empty n.val n.property)⟩

@[simp]
lemma outsideJ_empty (B : Finset ℕ) (q : TailParam A B) :
    outsideJ A B q (emptyOutside A B) = 1 := by
  rw [outsideJ_apply]
  change (∏ n : (∅ : Finset {n // n ∉ B}), _) = 1
  simp

lemma outsideJ_restrictParam (B : Finset ℕ) (q : Param A) :
    outsideJ A B (restrictParam A B q) = outsideJFull A B q := by
  ext c
  rw [outsideJ_apply, outsideJFull_apply]
  rfl

theorem split_j (B : Finset ℕ) (q : Param A) :
    split A B (j A q) = hilbertTensor (finitePacket A B (restrictHead A B q))
      (outsideJ A B (restrictParam A B q)) := by
  ext c
  rw [split_j_apply, hilbertTensor_apply, outsideJ_apply]
  rfl

lemma continuous_outsideJ (B : Finset ℕ) : Continuous (outsideJ A B) :=
  ((hilbertRow (emptyHead A B)).continuous.comp
    ((split A B).continuous.comp (continuous_j A))).comp (continuous_fillParam A B)

lemma norm_outsideJ_le (B : Finset ℕ) (q : TailParam A B) :
    ‖outsideJ A B q‖ ≤ ∑' F, majorant F := by
  exact (norm_hilbertRow_le _ _).trans
    ((split A B).norm_map _ ▸ norm_j_le A (fillParam A B q))

def outsideSingleton (B : Finset ℕ) (n : {n // n ∉ B}) (c : (A n.val).Coord) :
    OutsideCoord A B :=
  ⟨{n}, fun m => (Finset.mem_singleton.mp m.property).symm ▸ c⟩

lemma outsideSingleton_injective (B : Finset ℕ) (n : {n // n ∉ B}) :
    Function.Injective (outsideSingleton A B n) := by
  intro c d h
  have he := eq_of_heq (Sigma.mk.inj_iff.mp h).2
  have hf := congrFun he (⟨n, Finset.mem_singleton_self n⟩ : ({n} : Finset {n // n ∉ B}))
  simpa [outsideSingleton] using hf

lemma outsideJ_singleton (B : Finset ℕ) (q : TailParam A B)
    (n : {n // n ∉ B}) (c : (A n.val).Coord) :
    outsideJ A B q (outsideSingleton A B n c) = beta A n.val * (A n.val).j (q n) c := by
  rw [outsideJ_apply]
  change (∏ m : ({n} : Finset {n // n ∉ B}), beta A m.val.val *
    (A m.val.val).j (q m.val) ((Finset.mem_singleton.mp m.property).symm ▸ c)) = _
  rw [Fintype.prod_eq_single (⟨n, Finset.mem_singleton_self n⟩ :
    ({n} : Finset {n // n ∉ B}))]
  intro m hm
  exact (hm (Subtype.ext (Finset.mem_singleton.mp m.property))).elim

def outsideRecover (B : Finset ℕ) (n : {n // n ∉ B}) :
    OutsideSpace A B →L[ℝ] (A n.val).Space :=
  (beta A n.val)⁻¹ • hilbertRestrict
    ⟨outsideSingleton A B n, outsideSingleton_injective A B n⟩

@[simp]
lemma outsideRecover_j (B : Finset ℕ) (q : TailParam A B) (n : {n // n ∉ B}) :
    outsideRecover A B n (outsideJ A B q) = (A n.val).j (q n) := by
  ext c
  change (beta A n.val)⁻¹ * outsideJ A B q (outsideSingleton A B n c) = _
  rw [outsideJ_singleton, ← mul_assoc, inv_mul_cancel₀ (beta_ne_zero A n.val), one_mul]

lemma outsideJ_injective (B : Finset ℕ) : Function.Injective (outsideJ A B) := by
  intro q r h
  funext n
  apply (A n.val).closedEmbedding.injective
  have he := congrArg (outsideRecover A B n) h
  simpa using he

lemma exists_tendsto_of_tendsto_outsideJ (B : Finset ℕ) (u : ℕ → TailParam A B)
    {z : OutsideSpace A B} (hz : Tendsto (fun m => outsideJ A B (u m)) atTop (𝓝 z)) :
    ∃ q : TailParam A B, Tendsto u atTop (𝓝 q) := by
  have hrec (n : {n // n ∉ B}) : Tendsto (fun m => (A n.val).j (u m n)) atTop
      (𝓝 (outsideRecover A B n z)) := by
    simpa only [Function.comp_def, outsideRecover_j] using
      ((outsideRecover A B n).continuous.tendsto z).comp hz
  have hmem (n : {n // n ∉ B}) : outsideRecover A B n z ∈ range (A n.val).j :=
    (A n.val).closedEmbedding.isClosed_range.mem_of_tendsto (hrec n)
      (Eventually.of_forall fun m => mem_range_self (u m n))
  choose q hq using hmem
  refine ⟨q, tendsto_pi_nhds.2 fun n => ?_⟩
  apply (A n.val).closedEmbedding.tendsto_nhds_iff.2
  simpa only [Function.comp_def, hq] using hrec n

lemma isClosedMap_outsideJ (B : Finset ℕ) : IsClosedMap (outsideJ A B) := by
  intro C hC
  apply isSeqClosed_iff_isClosed.mp
  intro u z hu hz
  choose v hv hvj using hu
  have hvlim : Tendsto (fun m => outsideJ A B (v m)) atTop (𝓝 z) := by
    simpa only [hvj] using hz
  obtain ⟨q, hq⟩ := exists_tendsto_of_tendsto_outsideJ A B v hvlim
  refine ⟨q, hC.mem_of_tendsto hq (Eventually.of_forall hv), ?_⟩
  exact tendsto_nhds_unique ((continuous_outsideJ A B).continuousAt.tendsto.comp hq) hvlim

theorem isClosedEmbedding_outsideJ (B : Finset ℕ) : IsClosedEmbedding (outsideJ A B) :=
  IsClosedEmbedding.of_continuous_injective_isClosedMap
    (continuous_outsideJ A B) (outsideJ_injective A B) (isClosedMap_outsideJ A B)

/-- Mix a finite-head coefficient with an outside packet in the original Hilbert coordinates. -/
def mix (B : Finset ℕ) (v : HeadSpace A B) (q : TailParam A B) : Space A :=
  (split A B).symm (hilbertTensor v (outsideJ A B q))

lemma continuous_mix (B : Finset ℕ) :
    Continuous fun p : HeadSpace A B × TailParam A B => mix A B p.1 p.2 := by
  exact (split A B).symm.continuous.comp (continuous_hilbertTensor.comp
    (continuous_fst.prodMk ((continuous_outsideJ A B).comp continuous_snd)))

lemma norm_mix (B : Finset ℕ) (v : HeadSpace A B) (q : TailParam A B) :
    ‖mix A B v q‖ = ‖v‖ * ‖outsideJ A B q‖ := by
  rw [mix, (split A B).symm.norm_map, norm_hilbertTensor]

lemma mix_add (B : Finset ℕ) (v w : HeadSpace A B) (q : TailParam A B) :
    mix A B (v + w) q = mix A B v q + mix A B w q := by
  simp only [mix, hilbertTensor_add_left, map_add]

lemma mix_smul (B : Finset ℕ) (r : ℝ) (v : HeadSpace A B) (q : TailParam A B) :
    mix A B (r • v) q = r • mix A B v q := by
  simp only [mix, hilbertTensor_smul_left, map_smul]

def contractHead (B : Finset ℕ) (a : HeadCoord A B →₀ ℝ) :
    Space A →L[ℝ] OutsideSpace A B :=
  (hilbertContractLeft a).comp (split A B).toContinuousLinearEquiv.toContinuousLinearMap

def contractTail (B : Finset ℕ) (b : OutsideCoord A B →₀ ℝ) :
    Space A →L[ℝ] HeadSpace A B :=
  (hilbertContractRight b).comp (split A B).toContinuousLinearEquiv.toContinuousLinearMap

lemma contractHead_mix (B : Finset ℕ) (a : HeadCoord A B →₀ ℝ)
    (v : HeadSpace A B) (q : TailParam A B) :
    contractHead A B a (mix A B v q) = hilbertFinsuppFunctional a v • outsideJ A B q := by
  change hilbertContractLeft a ((split A B) ((split A B).symm
    (hilbertTensor v (outsideJ A B q)))) = _
  rw [LinearIsometryEquiv.apply_symm_apply, hilbertContractLeft_tensor]

lemma contractTail_mix (B : Finset ℕ) (b : OutsideCoord A B →₀ ℝ)
    (v : HeadSpace A B) (q : TailParam A B) :
    contractTail A B b (mix A B v q) = hilbertFinsuppFunctional b (outsideJ A B q) • v := by
  change hilbertContractRight b ((split A B) ((split A B).symm
    (hilbertTensor v (outsideJ A B q)))) = _
  rw [LinearIsometryEquiv.apply_symm_apply, hilbertContractRight_tensor]

lemma mix_finitePacket (B : Finset ℕ) (p : HeadParam A B) (q : TailParam A B) :
    mix A B (finitePacket A B p) q = j A (combineParam A B p q) := by
  apply (split A B).injective
  rw [split_j]
  simp only [restrictHead_combineParam, restrictParam_combineParam, mix,
    LinearIsometryEquiv.apply_symm_apply]

lemma j_eq_mix (B : Finset ℕ) (q : Param A) :
    j A q = mix A B (finitePacket A B (restrictHead A B q)) (restrictParam A B q) := by
  rw [mix_finitePacket, combineParam_restrict]

lemma mix_mem_span (B : Finset ℕ) {v : HeadSpace A B}
    (hv : v ∈ Submodule.span ℝ (range (finitePacket A B))) (q : TailParam A B) :
    mix A B v q ∈ span A := by
  induction hv using Submodule.span_induction with
  | mem v hv =>
    obtain ⟨p, rfl⟩ := hv
    rw [mix_finitePacket]
    exact Submodule.subset_span ⟨_, rfl⟩
  | zero =>
    have hzero : hilbertTensor (0 : HeadSpace A B) (outsideJ A B q) = 0 := by
      ext c
      simp only [hilbertTensor_apply, lp.coeFn_zero, Pi.zero_apply, zero_mul]
    rw [mix, hzero, map_zero]
    exact (span A).zero_mem
  | add v w _ _ hv hw =>
    rw [mix_add]
    exact (span A).add_mem hv hw
  | smul r v _ hv =>
    rw [mix_smul]
    exact (span A).smul_mem r hv

end NoUniversalFSigma.Proof.Packet
