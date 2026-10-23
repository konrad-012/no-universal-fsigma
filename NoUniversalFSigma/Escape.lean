module

public import NoUniversalFSigma.Rank

@[expose] public section

/-! The source derivative detects sums with limits outside the ambient subgroup. -/

namespace NoUniversalFSigma.Proof

open Set Filter Topology TopologicalSpace OrdinalApprox

variable {P B : Type} [TopologicalSpace P] [AddCommGroup B] [TopologicalSpace B]

def pairSum (j : P → B) (p : P × P) : B := j p.1 + j p.2

/-- Remove open neighborhoods whose sums have all ambient limits inside `H`. -/
def escapeDerivative (j : P → B) (H : AddSubgroup B) (R : Set (P × P)) : Set (P × P) :=
  R \ ⋃₀ {U : Set (P × P) | IsOpen U ∧ closure (pairSum j '' (R ∩ U)) ⊆ (H : Set B)}

theorem mem_escapeDerivative_iff (j : P → B) (H : AddSubgroup B)
    (R : Set (P × P)) (p : P × P) :
    p ∈ escapeDerivative j H R ↔ p ∈ R ∧
      ∀ U : Set (P × P), IsOpen U → p ∈ U →
        ¬ closure (pairSum j '' (R ∩ U)) ⊆ (H : Set B) := by
  constructor
  · rintro ⟨hp, hnot⟩
    exact ⟨hp, fun U hU hpU hbound => hnot ⟨U, ⟨hU, hbound⟩, hpU⟩⟩
  · rintro ⟨hp, hloc⟩
    refine ⟨hp, ?_⟩
    rintro ⟨U, ⟨hU, hbound⟩, hpU⟩
    exact hloc U hU hpU hbound

theorem escapeDerivative_subset (j : P → B) (H : AddSubgroup B) (R : Set (P × P)) :
    escapeDerivative j H R ⊆ R := sdiff_subset

theorem escapeDerivative_mono (j : P → B) (H : AddSubgroup B) :
    Monotone (escapeDerivative j H) := by
  intro R S hRS p hp
  rw [mem_escapeDerivative_iff] at hp ⊢
  refine ⟨hRS hp.1, fun U hU hpU hbound => hp.2 U hU hpU ?_⟩
  exact (closure_mono (image_mono (inter_subset_inter_left U hRS))).trans hbound

theorem isClosed_escapeDerivative (j : P → B) (H : AddSubgroup B) {R : Set (P × P)}
    (hR : IsClosed R) : IsClosed (escapeDerivative j H R) :=
  hR.sdiff (isOpen_sUnion fun _U hU => hU.1)

def escapeDerivativeOrderHom (j : P → B) (H : AddSubgroup B) : Set (P × P) →o Set (P × P) :=
  ⟨escapeDerivative j H, escapeDerivative_mono j H⟩

def escapeRemainderFrom (j : P → B) (H : AddSubgroup B) (R : Set (P × P)) :
    Ordinal → Set (P × P) := gfpApprox (escapeDerivativeOrderHom j H) R

def escapeRemainder (j : P → B) (H : AddSubgroup B) : Ordinal → Set (P × P) :=
  escapeRemainderFrom j H univ

@[simp] theorem escapeRemainderFrom_zero (j : P → B) (H : AddSubgroup B)
    (R : Set (P × P)) : escapeRemainderFrom j H R 0 = R := gfpApprox_zero _

@[simp] theorem escapeRemainderFrom_add_one (j : P → B) (H : AddSubgroup B)
    (R : Set (P × P)) (a : Ordinal) :
    escapeRemainderFrom j H R (a + 1) =
      escapeDerivative j H (escapeRemainderFrom j H R a) :=
  gfpApprox_add_one _ (escapeDerivative_subset j H R) a

theorem escapeRemainderFrom_limit (j : P → B) (H : AddSubgroup B)
    (R : Set (P × P)) {a : Ordinal} (ha : Order.IsSuccLimit a) :
    escapeRemainderFrom j H R a = ⋂ b : Iio a, escapeRemainderFrom j H R b.1 :=
  gfpApprox_of_isSuccLimit _ ha

theorem escapeRemainderFrom_antitone (j : P → B) (H : AddSubgroup B) (R : Set (P × P)) :
    Antitone (escapeRemainderFrom j H R) := gfpApprox_anti_right _

theorem escapeRemainderFrom_subset (j : P → B) (H : AddSubgroup B)
    (R : Set (P × P)) (a : Ordinal) : escapeRemainderFrom j H R a ⊆ R := gfpApprox_le _

theorem isClosed_escapeRemainderFrom (j : P → B) (H : AddSubgroup B)
    {R : Set (P × P)} (hR : IsClosed R) (a : Ordinal) :
    IsClosed (escapeRemainderFrom j H R a) := by
  induction a using Ordinal.limitRecOn with
  | zero => simpa using hR
  | add_one a ih => simpa using isClosed_escapeDerivative j H ih
  | limit a ha ih =>
    rw [escapeRemainderFrom_limit j H R ha]
    exact isClosed_iInter fun b => ih b.1 b.2

@[simp] theorem escapeRemainder_zero (j : P → B) (H : AddSubgroup B) :
    escapeRemainder j H 0 = univ := escapeRemainderFrom_zero _ _ _

@[simp] theorem escapeRemainder_add_one (j : P → B) (H : AddSubgroup B) (a : Ordinal) :
    escapeRemainder j H (a + 1) = escapeDerivative j H (escapeRemainder j H a) :=
  escapeRemainderFrom_add_one _ _ _ _

theorem escapeRemainder_limit (j : P → B) (H : AddSubgroup B) {a : Ordinal}
    (ha : Order.IsSuccLimit a) :
    escapeRemainder j H a = ⋂ b : Iio a, escapeRemainder j H b.1 :=
  escapeRemainderFrom_limit _ _ _ ha

theorem escapeRemainder_antitone (j : P → B) (H : AddSubgroup B) :
    Antitone (escapeRemainder j H) := escapeRemainderFrom_antitone _ _ _

theorem isClosed_escapeRemainder (j : P → B) (H : AddSubgroup B) (a : Ordinal) :
    IsClosed (escapeRemainder j H a) := isClosed_escapeRemainderFrom _ _ isClosed_univ _

/-- An escape can be witnessed by a sequence of pairs in any prescribed neighborhood.
Only the sums are required to converge. -/
theorem exists_escape_sequence [FirstCountableTopology B] (j : P → B) (H : AddSubgroup B)
    {R : Set (P × P)} {p : P × P} (hp : p ∈ escapeDerivative j H R)
    {U : Set (P × P)} (hU : IsOpen U) (hpU : p ∈ U) :
    ∃ z : B, z ∉ H ∧ ∃ q : ℕ → P × P,
      (∀ l, q l ∈ R) ∧ (∀ l, q l ∈ U) ∧ Tendsto (fun l => pairSum j (q l)) atTop (𝓝 z) := by
  have hnot := ((mem_escapeDerivative_iff j H R p).mp hp).2 U hU hpU
  obtain ⟨z, hz, hzH⟩ := not_subset.mp hnot
  obtain ⟨v, hv, hvlim⟩ := mem_closure_iff_seq_limit.mp hz
  choose q hq hqv using hv
  refine ⟨z, hzH, q, fun l => (hq l).1, fun l => (hq l).2, ?_⟩
  simpa only [hqv] using hvlim

/-- The derivative is local on an open part of its pair parameter space. -/
theorem escapeDerivative_inter_open (j : P → B) (H : AddSubgroup B)
    (R W : Set (P × P)) (hW : IsOpen W) :
    escapeDerivative j H (R ∩ W) = escapeDerivative j H R ∩ W := by
  ext p
  constructor
  · intro hp
    have hp' := (mem_escapeDerivative_iff j H (R ∩ W) p).mp hp
    exact ⟨escapeDerivative_mono j H inter_subset_left hp, hp'.1.2⟩
  · rintro ⟨hp, hpW⟩
    have hp' := (mem_escapeDerivative_iff j H R p).mp hp
    apply (mem_escapeDerivative_iff j H (R ∩ W) p).mpr
    refine ⟨⟨hp'.1, hpW⟩, fun U hU hpU hbound => hp'.2 (U ∩ W) (hU.inter hW) ⟨hpU, hpW⟩ ?_⟩
    exact (closure_mono (image_mono (by
      intro q hq
      exact ⟨⟨hq.1, hq.2.2⟩, hq.2.1⟩))).trans hbound

theorem escapeRemainderFrom_inter_open (j : P → B) (H : AddSubgroup B)
    (R W : Set (P × P)) (hW : IsOpen W) (a : Ordinal) :
    escapeRemainderFrom j H (R ∩ W) a = escapeRemainderFrom j H R a ∩ W := by
  induction a using Ordinal.limitRecOn with
  | zero => simp
  | add_one a ih =>
    simp only [escapeRemainderFrom_add_one, ih, escapeDerivative_inter_open j H _ _ hW]
  | limit a ha ih =>
    rw [escapeRemainderFrom_limit j H (R ∩ W) ha, escapeRemainderFrom_limit j H R ha]
    ext p
    simp only [mem_iInter, mem_inter_iff, Subtype.forall]
    constructor
    · intro hp
      exact ⟨fun b hb => (by have hpb := hp b hb; rw [ih b hb] at hpb; exact hpb.1),
        (by have := hp 0 ha.bot_lt; rw [ih 0 ha.bot_lt] at this; exact this.2)⟩
    · rintro ⟨hp, hpW⟩ b hb
      rw [ih b hb]
      exact ⟨hp b hb, hpW⟩

section Transfer

variable {Q C : Type} [TopologicalSpace Q] [AddCommGroup C] [TopologicalSpace C]

/-- Continuous changes of pair parameters and a continuous map of ambient sums transfer
escapes whenever that map sends points outside the source subgroup outside the target. -/
theorem escapeDerivative_transfer (i : Q → C) (K : AddSubgroup C)
    (j : P → B) (H : AddSubgroup B) (a b : Q → P)
    (ha : Continuous a) (hb : Continuous b) (L : C → B) (hL : Continuous L)
    (hsum : ∀ t u, pairSum j (a t, b u) = L (pairSum i (t, u)))
    (hout : ∀ z, z ∉ K → L z ∉ H) {R : Set (Q × Q)} {S : Set (P × P)}
    (hmap : ∀ q ∈ R, (a q.1, b q.2) ∈ S) {p : Q × Q}
    (hp : p ∈ escapeDerivative i K R) : (a p.1, b p.2) ∈ escapeDerivative j H S := by
  have hpc := (mem_escapeDerivative_iff i K R p).mp hp
  apply (mem_escapeDerivative_iff j H S _).mpr
  refine ⟨hmap p hpc.1, fun U hU hpU hbound => ?_⟩
  let g : Q × Q → P × P := fun q => (a q.1, b q.2)
  have hg : Continuous g := (ha.comp continuous_fst).prodMk (hb.comp continuous_snd)
  have hn := hpc.2 (g ⁻¹' U) (hU.preimage hg) hpU
  obtain ⟨z, hz, hzK⟩ := not_subset.mp hn
  apply hout z hzK
  apply hbound
  have hzL : L z ∈ closure (L '' (pairSum i '' (R ∩ g ⁻¹' U))) :=
    image_closure_subset_closure_image hL ⟨z, hz, rfl⟩
  apply closure_mono (t := pairSum j '' (S ∩ U)) ?_ hzL
  rintro w ⟨v, ⟨q, hq, rfl⟩, rfl⟩
  exact ⟨g q, ⟨hmap q hq.1, hq.2⟩, hsum q.1 q.2⟩

theorem escapeRemainder_transfer (i : Q → C) (K : AddSubgroup C)
    (j : P → B) (H : AddSubgroup B) (a b : Q → P)
    (ha : Continuous a) (hb : Continuous b) (L : C → B) (hL : Continuous L)
    (hsum : ∀ t u, pairSum j (a t, b u) = L (pairSum i (t, u)))
    (hout : ∀ z, z ∉ K → L z ∉ H) (o : Ordinal) :
    ∀ p ∈ escapeRemainder i K o, (a p.1, b p.2) ∈ escapeRemainder j H o := by
  induction o using Ordinal.limitRecOn with
  | zero => simp
  | add_one o ih =>
    simp only [escapeRemainder_add_one]
    exact fun p hp => escapeDerivative_transfer i K j H a b ha hb L hL hsum hout ih hp
  | limit o ho ih =>
    simp only [escapeRemainder_limit _ _ ho, mem_iInter]
    intro p hp c
    exact ih c.1 c.2 p (hp c)

end Transfer

end NoUniversalFSigma.Proof
