module

public import NoUniversalFSigma.PacketFeatures
public import NoUniversalFSigma.PacketChartData

@[expose] public section

/-! Finite-coordinate recovery from pinned packet mixtures. -/

noncomputable section

open Set
open scoped lp

namespace NoUniversalFSigma.Proof.Packet

attribute [local instance] Classical.propDecidable

variable (A : ℕ → AdmissibleFamily) (B : Finset ℕ)

abbrev WitnessCoord (W : Finset {n // n ∉ B}) :=
  ∀ w : W, Option (A w.val.val).Coord

abbrev RemainderCoord (W : Finset {n // n ∉ B}) :=
  PacketSplit.Coord (fun n : {n : {n // n ∉ B} // n ∉ W} => (A n.val.val).Coord)

def witnessPacket (W : Finset {n // n ∉ B}) (q : TailParam A B) :
    ℓ²(WitnessCoord A B W, ℝ) :=
  hilbertPi W (fun w => Option (A w.val.val).Coord)
    (fun w => oneFactor A w.val.val (q w.val))

def witnessFunctional (W : Finset {n // n ∉ B}) (a : WitnessFeature A B W) :
    WitnessCoord A B W →₀ ℝ :=
  finsuppPi W (fun w => Option (A w.val.val).Coord)
    (fun w => oneFactorFeature A w.val.val (a w))

lemma witnessFunctional_apply (W : Finset {n // n ∉ B}) (a : WitnessFeature A B W)
    (q : TailParam A B) :
    hilbertFinsuppFunctional (witnessFunctional A B W a) (witnessPacket A B W q) =
      witnessValue A B W a q := by
  rw [witnessFunctional, witnessPacket, hilbertFinsuppFunctional_finsuppPi]
  exact Finset.prod_congr rfl fun w _ => oneFactorFeature_apply A w.val.val (a w) (q w.val)

def remainderEmpty (W : Finset {n // n ∉ B}) : RemainderCoord A B W :=
  ⟨∅, fun n => False.elim (Finset.notMem_empty n.val n.property)⟩

def witnessMerge (W : Finset {n // n ∉ B}) (h : WitnessCoord A B W)
    (t : RemainderCoord A B W) : OutsideCoord A B :=
  (PacketSplit.coordSplit (fun n : {n // n ∉ B} => (A n.val).Coord) W).symm (h, t)

lemma outsideJ_witnessMerge (W : Finset {n // n ∉ B}) (q : TailParam A B)
    (h : WitnessCoord A B W) (t : RemainderCoord A B W) :
    outsideJ A B q (witnessMerge A B W h t) = witnessPacket A B W q h *
      PacketSplit.coordProduct
        (fun n : {n : {n // n ∉ B} // n ∉ W} => (A n.val.val).Coord)
        (fun n d => beta A n.val.val * (A n.val.val).j (q n.val) d) t := by
  rw [outsideJ_apply]
  have hs := PacketSplit.coordProduct_split (fun n : {n // n ∉ B} => (A n.val).Coord) W
    (fun n d => beta A n.val * (A n.val).j (q n) d) (witnessMerge A B W h t)
  simp only [witnessMerge, Equiv.apply_symm_apply] at hs
  change PacketSplit.coordProduct (fun n : {n // n ∉ B} => (A n.val).Coord)
    (fun n d => beta A n.val * (A n.val).j (q n) d)
      ((PacketSplit.coordSplit (fun n : {n // n ∉ B} => (A n.val).Coord) W).symm (h, t)) = _
  rw [hs]
  congr 1
  rw [witnessPacket, hilbertPi_apply]
  apply Finset.prod_congr rfl
  intro w _
  cases h w with
  | none => rw [oneFactor_none]; rfl
  | some c => rfl

def witnessEmbedding (W : Finset {n // n ∉ B}) :
    WitnessCoord A B W ↪ OutsideCoord A B where
  toFun h := witnessMerge A B W h (remainderEmpty A B W)
  inj' := by
    intro h k he
    exact (Prod.mk.inj ((PacketSplit.coordSplit _ W).symm.injective he)).1

lemma outsideJ_witnessEmbedding (W : Finset {n // n ∉ B}) (q : TailParam A B)
    (h : WitnessCoord A B W) :
    outsideJ A B q (witnessEmbedding A B W h) = witnessPacket A B W q h := by
  change outsideJ A B q (witnessMerge A B W h (remainderEmpty A B W)) = _
  rw [outsideJ_witnessMerge]
  change _ * (∏ n : (∅ : Finset {n : {n // n ∉ B} // n ∉ W}), _) = _
  simp

def witnessLift (W : Finset {n // n ∉ B}) (a : WitnessCoord A B W →₀ ℝ) :
    OutsideCoord A B →₀ ℝ := a.embDomain (witnessEmbedding A B W)

lemma witnessLift_outsideJ (W : Finset {n // n ∉ B}) (a : WitnessCoord A B W →₀ ℝ)
    (q : TailParam A B) :
    hilbertFinsuppFunctional (witnessLift A B W a) (outsideJ A B q) =
      hilbertFinsuppFunctional a (witnessPacket A B W q) := by
  simp only [hilbertFinsuppFunctional_apply, witnessLift, Finsupp.support_embDomain,
    Finset.sum_map]
  apply Finset.sum_congr rfl
  intro h _
  rw [Finsupp.embDomain_apply_self, outsideJ_witnessEmbedding]

def coefficientRecovery (W : Finset {n // n ∉ B}) (a : WitnessFeature A B W) :
    Space A →L[ℝ] HeadSpace A B :=
  contractTail A B (witnessLift A B W (witnessFunctional A B W a))

lemma coefficientRecovery_mix (W : Finset {n // n ∉ B}) (a : WitnessFeature A B W)
    (v : HeadSpace A B) (q : TailParam A B) :
    coefficientRecovery A B W a (mix A B v q) = witnessValue A B W a q • v := by
  rw [coefficientRecovery, contractTail_mix, witnessLift_outsideJ, witnessFunctional_apply]

def remainderSingleton (W : Finset {n // n ∉ B}) (n : {n // n ∉ B}) (hn : n ∉ W)
    (c : (A n.val).Coord) : RemainderCoord A B W :=
  ⟨{⟨n, hn⟩}, fun m => (Finset.mem_singleton.mp m.property).symm ▸ c⟩

lemma remainderSingleton_injective (W : Finset {n // n ∉ B}) (n : {n // n ∉ B})
    (hn : n ∉ W) : Function.Injective (remainderSingleton A B W n hn) := by
  intro c d h
  have he := eq_of_heq (Sigma.mk.inj_iff.mp h).2
  have hf := congrFun he (⟨⟨n, hn⟩, Finset.mem_singleton_self _⟩ :
    ({⟨n, hn⟩} : Finset {n : {n // n ∉ B} // n ∉ W}))
  simpa [remainderSingleton] using hf

def witnessTailEmbedding (W : Finset {n // n ∉ B}) (h : WitnessCoord A B W)
    (n : {n // n ∉ B}) (hn : n ∉ W) : (A n.val).Coord ↪ OutsideCoord A B where
  toFun c := witnessMerge A B W h (remainderSingleton A B W n hn c)
  inj' := by
    intro c d he
    apply remainderSingleton_injective A B W n hn
    exact (Prod.mk.inj ((PacketSplit.coordSplit _ W).symm.injective he)).2

lemma outsideJ_witnessTailEmbedding (W : Finset {n // n ∉ B}) (q : TailParam A B)
    (h : WitnessCoord A B W) (n : {n // n ∉ B}) (hn : n ∉ W) (c : (A n.val).Coord) :
    outsideJ A B q (witnessTailEmbedding A B W h n hn c) =
      witnessPacket A B W q h * (beta A n.val * (A n.val).j (q n) c) := by
  change outsideJ A B q (witnessMerge A B W h (remainderSingleton A B W n hn c)) = _
  rw [outsideJ_witnessMerge]
  congr 1
  change (∏ m : ({⟨n, hn⟩} : Finset {n : {n // n ∉ B} // n ∉ W}),
    beta A m.val.val.val * (A m.val.val.val).j (q m.val.val)
      ((Finset.mem_singleton.mp m.property).symm ▸ c)) = _
  rw [Fintype.prod_eq_single (⟨⟨n, hn⟩, Finset.mem_singleton_self _⟩ :
    ({⟨n, hn⟩} : Finset {n : {n // n ∉ B} // n ∉ W}))]
  intro m hm
  exact (hm (Subtype.ext (Finset.mem_singleton.mp m.property))).elim

def witnessRecovery (W : Finset {n // n ∉ B}) (a : WitnessCoord A B W →₀ ℝ)
    (n : {n // n ∉ B}) (hn : n ∉ W) : OutsideSpace A B →L[ℝ] (A n.val).Space :=
  (beta A n.val)⁻¹ • ∑ h ∈ a.support,
    a h • hilbertRestrict (witnessTailEmbedding A B W h n hn)

lemma witnessRecovery_outsideJ (W : Finset {n // n ∉ B}) (a : WitnessCoord A B W →₀ ℝ)
    (q : TailParam A B) (n : {n // n ∉ B}) (hn : n ∉ W) :
    witnessRecovery A B W a n hn (outsideJ A B q) =
      hilbertFinsuppFunctional a (witnessPacket A B W q) • (A n.val).j (q n) := by
  ext c
  simp only [witnessRecovery, smul_apply, sum_apply,
    lp.coeFn_smul, Pi.smul_apply, lp.coeFn_sum, Finset.sum_apply, hilbertRestrict_apply,
    smul_eq_mul, outsideJ_witnessTailEmbedding, hilbertFinsuppFunctional_apply]
  change (beta A n.val)⁻¹ * (∑ h ∈ a.support, a h *
    (witnessPacket A B W q h * (beta A n.val * (A n.val).j (q n) c))) = _
  have hs : (∑ h ∈ a.support, a h *
      (witnessPacket A B W q h * (beta A n.val * (A n.val).j (q n) c))) =
      (∑ h ∈ a.support, a h * witnessPacket A B W q h) *
        (beta A n.val * (A n.val).j (q n) c) := by
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro h _
    ring
  rw [hs]
  field_simp [beta_ne_zero A n.val]

def tailRecovery (W : Finset {n // n ∉ B}) (a : WitnessFeature A B W)
    (coord : HeadCoord A B) (n : {n // n ∉ B}) (hn : n ∉ W) :
    Space A →L[ℝ] (A n.val).Space :=
  (witnessRecovery A B W (witnessFunctional A B W a) n hn).comp
    (contractHead A B (Finsupp.single coord 1))

lemma tailRecovery_mix (W : Finset {n // n ∉ B}) (a : WitnessFeature A B W)
    (coord : HeadCoord A B) (n : {n // n ∉ B}) (hn : n ∉ W)
    (v : HeadSpace A B) (q : TailParam A B) :
    tailRecovery A B W a coord n hn (mix A B v q) =
      (v coord * witnessValue A B W a q) • (A n.val).j (q n) := by
  rw [tailRecovery, ContinuousLinearMap.comp_apply, contractHead_mix, map_smul,
    witnessRecovery_outsideJ, witnessFunctional_apply, smul_smul]
  simp [hilbertFinsuppFunctional_apply]

lemma tailRecovery_sum (W : Finset {n // n ∉ B}) (a : WitnessFeature A B W)
    (coord : HeadCoord A B) (n : {n // n ∉ B}) (hn : n ∉ W) {m : ℕ}
    (v : Fin m → HeadSpace A B) (q : Fin m → TailParam A B) (c : Fin m)
    (hp : ∀ e, witnessValue A B W a (q e) = if c = e then 1 else 0) :
    tailRecovery A B W a coord n hn (∑ e, mix A B (v e) (q e)) =
      v c coord • (A n.val).j (q c n) := by
  rw [map_sum]
  calc
    (∑ e, tailRecovery A B W a coord n hn (mix A B (v e) (q e))) =
        ∑ e, (v e coord * witnessValue A B W a (q e)) • (A n.val).j (q e n) :=
      Finset.sum_congr rfl fun e _ => tailRecovery_mix A B W a coord n hn (v e) (q e)
    _ = _ := by
      rw [Finset.sum_eq_single c]
      · rw [hp c, ite_eq_left rfl, mul_one]
      · intro e _ he
        rw [hp e, ite_eq_right (Ne.symm he), mul_zero, zero_smul]
      · intro hc
        exact (hc (Finset.mem_univ c)).elim

variable {B}

def chartCoeff (d : TensorChartIndex A) (c : Fin d.size) : Space A →L[ℝ] HeadSpace A d.B :=
  coefficientRecovery A d.B d.W1 (d.feature1 c)

def chartRecover (d : TensorChartIndex A) (c : Fin d.size) (n : {n // n ∉ d.B}) :
    Space A →L[ℝ] (A n.val).Space :=
  if hn : n ∉ d.W1 then tailRecovery A d.B d.W1 (d.feature1 c) (d.coord c) n hn
  else tailRecovery A d.B d.W2 (d.feature2 c) (d.coord c) n
    (fun h2 => Finset.disjoint_left.mp d.disjoint (not_not.mp hn) h2)

lemma chartCoeff_sum (d : TensorChartIndex A) (v : Fin d.size → HeadSpace A d.B)
    (q : Fin d.size → TailParam A d.B) (hq : q ∈ pinSet A d) (c : Fin d.size) :
    chartCoeff A d c (∑ e, mix A d.B (v e) (q e)) = v c := by
  rw [map_sum]
  simp only [chartCoeff, coefficientRecovery_mix, (hq c _).1]
  simp

lemma chartRecover_sum (d : TensorChartIndex A) (v : Fin d.size → HeadSpace A d.B)
    (q : Fin d.size → TailParam A d.B) (hq : q ∈ pinSet A d)
    (c : Fin d.size) (n : {n // n ∉ d.B}) :
    chartRecover A d c n (∑ e, mix A d.B (v e) (q e)) =
      v c (d.coord c) • (A n.val).j (q c n) := by
  by_cases hn : n ∉ d.W1
  · rw [chartRecover, dite_eq_left hn]
    exact tailRecovery_sum A d.B d.W1 (d.feature1 c) (d.coord c) n hn v q c
      (fun e => (hq c e).1)
  · rw [chartRecover, dite_eq_right hn]
    exact tailRecovery_sum A d.B d.W2 (d.feature2 c) (d.coord c) n _ v q c
      (fun e => (hq c e).2)

end NoUniversalFSigma.Proof.Packet
