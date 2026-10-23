module

public import NoUniversalFSigma.Basic
public import NoUniversalFSigma.Escape
public import NoUniversalFSigma.TargetRank

@[expose] public section

/-! Baire-measurable reductions compare escape and composition derivatives. -/

namespace NoUniversalFSigma.Proof

open Set Filter Topology TopologicalSpace NoUniversalFSigma

variable {P B Y : Type} [TopologicalSpace P]
  [NormedAddCommGroup B] [TopologicalSpace Y]

/-- Parameter-dependent translation is a homeomorphism of the product. -/
def parameterTranslation (j : P → B) (hj : Continuous j) : B × P ≃ₜ B × P where
  toFun p := (p.1 + j p.2, p.2)
  invFun p := (p.1 - j p.2, p.2)
  left_inv p := by ext <;> simp
  right_inv p := by ext <;> simp
  continuous_toFun := (continuous_fst.add (hj.comp continuous_snd)).prodMk continuous_snd
  continuous_invFun := (continuous_fst.sub (hj.comp continuous_snd)).prodMk continuous_snd

theorem isOpenMap_parameter_add (j : P → B) (hj : Continuous j) :
    IsOpenMap (fun p : B × P => p.1 + j p.2) :=
  isOpenMap_fst.comp (parameterTranslation j hj).isOpenMap

theorem isOpenMap_parameter_sub (j : P → B) (hj : Continuous j) :
    IsOpenMap (fun p : B × P => p.1 - j p.2) := by
  simpa only [sub_eq_add_neg] using isOpenMap_parameter_add (fun t => -j t) hj.neg

def goodDomain (j : P → B) (C : Set B) : Set (B × P) :=
  {p | p.1 ∈ C ∧ p.1 + j p.2 ∈ C ∧ p.1 - j p.2 ∈ C}

theorem isGδ_goodDomain (j : P → B) (hj : Continuous j) {C : Set B} (hC : IsGδ C) :
    IsGδ (goodDomain j C) :=
  (hC.preimage continuous_fst).inter
    ((hC.preimage (continuous_fst.add (hj.comp continuous_snd))).inter
      (hC.preimage (continuous_fst.sub (hj.comp continuous_snd))))

theorem residual_goodDomain (j : P → B) (hj : Continuous j) {C : Set B}
    (hC : C ∈ residual B) : goodDomain j C ∈ residual (B × P) := by
  filter_upwards [tendsto_residual_of_isOpenMap continuous_fst isOpenMap_fst hC,
    tendsto_residual_of_isOpenMap (continuous_fst.add (hj.comp continuous_snd))
      (isOpenMap_parameter_add j hj) hC,
    tendsto_residual_of_isOpenMap (continuous_fst.sub (hj.comp continuous_snd))
      (isOpenMap_parameter_sub j hj) hC] with p h0 hp hm
  exact ⟨h0, hp, hm⟩

theorem mem_closure_dense_inter_open {X : Type} [TopologicalSpace X]
    {D U : Set X} (hD : Dense D) (hU : IsOpen U) {p : X} (hp : p ∈ U) :
    p ∈ closure (D ∩ U) := by
  apply mem_closure_iff.mpr
  intro V hV hpV
  obtain ⟨q, ⟨hqV, hqU⟩, hqD⟩ := hD.inter_open_nonempty (V ∩ U) (hV.inter hU) ⟨p, hpV, hp⟩
  exact ⟨q, hqV, hqD, hqU⟩

/-- Extend a closed edge condition from a dense set, retaining continuity only on `C`. -/
theorem closed_edge_extension {X : Type} [TopologicalSpace X] [FirstCountableTopology X]
    (f : B → Y) {C : Set B} (hf : ContinuousOn f C)
    (e₁ e₂ : X → B) (h₁ : Continuous e₁) (h₂ : Continuous e₂)
    {D U : Set X} (hD : Dense D) (hU : IsOpen U)
    (hDC : ∀ q ∈ D, e₁ q ∈ C ∧ e₂ q ∈ C)
    {F : Set (Y × Y)} (hF : IsClosed F)
    (hbound : ∀ q ∈ D ∩ U, (f (e₁ q), f (e₂ q)) ∈ F)
    {p : X} (hpU : p ∈ U) (hp₁ : e₁ p ∈ C) (hp₂ : e₂ p ∈ C) :
    (f (e₁ p), f (e₂ p)) ∈ F := by
  obtain ⟨q, hq, hlim⟩ := mem_closure_iff_seq_limit.mp (mem_closure_dense_inter_open hD hU hpU)
  have he₁ : Tendsto (fun n => f (e₁ (q n))) atTop (𝓝 (f (e₁ p))) :=
    (hf _ hp₁).tendsto.comp (tendsto_nhdsWithin_iff.mpr
      ⟨h₁.continuousAt.tendsto.comp hlim, Eventually.of_forall fun n => (hDC _ (hq n).1).1⟩)
  have he₂ : Tendsto (fun n => f (e₂ (q n))) atTop (𝓝 (f (e₂ p))) :=
    (hf _ hp₂).tendsto.comp (tendsto_nhdsWithin_iff.mpr
      ⟨h₂.continuousAt.tendsto.comp hlim, Eventually.of_forall fun n => (hDC _ (hq n).1).2⟩)
  exact hF.mem_of_tendsto (he₁.prodMk_nhds he₂) (Eventually.of_forall fun n => hbound _ (hq n))

theorem exists_open_source_neighborhood (f : B → Y) {C : Set B} (hf : ContinuousOn f C)
    {x : B} (hx : x ∈ C) {U : Set Y} (hU : IsOpen U) (hfx : f x ∈ U) :
    ∃ N : Set B, IsOpen N ∧ x ∈ N ∧ ∀ y ∈ N, y ∈ C → f y ∈ U := by
  obtain ⟨N, hN, hxN, hmap⟩ := mem_nhdsWithin.mp
    ((hf x hx).preimage_mem_nhdsWithin (hU.mem_nhds hfx))
  exact ⟨N, hN, hxN, fun y hy hyC => hmap ⟨hy, hyC⟩⟩

theorem exists_shift_neighborhoods (j : P → B) (hj : Continuous j)
    (x : B) (t u : P) {NP N₀ NM : Set B}
    (hP : IsOpen NP) (h₀ : IsOpen N₀) (hM : IsOpen NM)
    (hxP : x + j t ∈ NP) (hx₀ : x ∈ N₀) (hxM : x - j u ∈ NM) :
    ∃ A : Set B, ∃ U V : Set P, IsOpen A ∧ x + j t ∈ A ∧ IsOpen U ∧ t ∈ U ∧
      IsOpen V ∧ u ∈ V ∧ ∀ v ∈ A, ∀ s ∈ U, ∀ r ∈ V,
        v ∈ NP ∧ v - j s ∈ N₀ ∧ v - j s - j r ∈ NM := by
  let g : B × P × P → B × B × B := fun p =>
    (p.1, p.1 - j p.2.1, p.1 - j p.2.1 - j p.2.2)
  have hg : Continuous g := continuous_fst.prodMk
    ((continuous_fst.sub (hj.comp (continuous_fst.comp continuous_snd))).prodMk
      ((continuous_fst.sub (hj.comp (continuous_fst.comp continuous_snd))).sub
        (hj.comp (continuous_snd.comp continuous_snd))))
  have hmem : g (x + j t, t, u) ∈ NP ×ˢ (N₀ ×ˢ NM) := by
    simpa only [g, add_sub_cancel_right, mem_prod] using (show x + j t ∈ NP ∧ x ∈ N₀ ∧ x - j u ∈ NM from
      ⟨hxP, hx₀, hxM⟩)
  obtain ⟨A, W, hA, hxA, hW, htuW, hAW⟩ := mem_nhds_prod_iff'.mp
    (((hP.prod (h₀.prod hM)).preimage hg).mem_nhds hmem)
  obtain ⟨U, V, hU, htU, hV, huV, hUV⟩ := mem_nhds_prod_iff'.mp (hW.mem_nhds htuW)
  refine ⟨A, U, V, hA, hxA, hU, htU, hV, huV, ?_⟩
  intro v hv s hs r hr
  have h := hAW (a := (v, s, r)) ⟨hv, hUV (a := (s, r)) ⟨hs, hr⟩⟩
  simpa only [mem_preimage, g, mem_prod] using h

theorem residual_sub {C : Set B} (hC : C ∈ residual B) (a : B) :
    ∀ᶠ v in residual B, v - a ∈ C := by
  have h := tendsto_residual_of_isOpenMap (Homeomorph.addRight (-a)).continuous
    (Homeomorph.addRight (-a)).isOpenMap hC
  change {v : B | v + -a ∈ C} ∈ residual B at h
  change {v : B | v - a ∈ C} ∈ residual B
  simpa only [sub_eq_add_neg] using h

variable [PolishSpace P] [PolishSpace B] [PolishSpace Y]

structure ReductionRectangle {E : EquivRel Y} (K : ClosedExhaustion E)
    (j : P → B) (f : B → Y) (C : Set B) where
  level : ℕ
  base : Set B
  param : Set P
  isOpen_base : IsOpen base
  isOpen_param : IsOpen param
  nonempty_base : base.Nonempty
  nonempty_param : param.Nonempty
  plus : ∀ x ∈ base, ∀ t ∈ param, x ∈ C → x + j t ∈ C → (f (x + j t), f x) ∈ K.piece level
  minus : ∀ x ∈ base, ∀ t ∈ param, x ∈ C → x - j t ∈ C → (f x, f (x - j t)) ∈ K.piece level

omit [PolishSpace Y] in
/-- A fixed closed target level controls both translated edges on an open rectangle. -/
theorem exists_reductionRectangle [Nonempty P] {E : EquivRel Y} (K : ClosedExhaustion E)
    (H : AddSubgroup B) (j : P → B) (hj : Continuous j) (hjH : ∀ t, j t ∈ H)
    (f : B → Y) (hred : IsReduction (cosetRel H) E f)
    {C : Set B} (hCG : IsGδ C) (hC : C ∈ residual B) (hf : ContinuousOn f C) :
    Nonempty (ReductionRectangle K j f C) := by
  classical
  let D := goodDomain j C
  have hDG : IsGδ D := isGδ_goodDomain j hj hCG
  have hDd : Dense D := dense_of_mem_residual (residual_goodDomain j hj hC)
  let : BaireSpace D := hDG.baireSpace_of_dense hDd
  let : Nonempty D := hDd.nonempty.to_subtype
  have h0 : Continuous (fun p : D => f p.1.1) :=
    hf.comp_continuous (continuous_fst.comp continuous_subtype_val) fun p => p.2.1
  have hp : Continuous (fun p : D => f (p.1.1 + j p.1.2)) :=
    hf.comp_continuous ((continuous_fst.add (hj.comp continuous_snd)).comp continuous_subtype_val)
      fun p => p.2.2.1
  have hm : Continuous (fun p : D => f (p.1.1 - j p.1.2)) :=
    hf.comp_continuous ((continuous_fst.sub (hj.comp continuous_snd)).comp continuous_subtype_val)
      fun p => p.2.2.2
  let Q : ℕ → Set D := fun n =>
    {p | (f (p.1.1 + j p.1.2), f p.1.1) ∈ K.piece n ∧
      (f p.1.1, f (p.1.1 - j p.1.2)) ∈ K.piece n}
  have hQclosed : ∀ n, IsClosed (Q n) := fun n =>
    ((K.isClosed_piece n).preimage (hp.prodMk h0)).inter
      ((K.isClosed_piece n).preimage (h0.prodMk hm))
  have hQcover : ⋃ n, Q n = univ := by
    ext p
    simp only [mem_iUnion, mem_univ, iff_true]
    have hplus : E.r (f (p.1.1 + j p.1.2)) (f p.1.1) :=
      (hred _ _).mp (by change p.1.1 + j p.1.2 - p.1.1 ∈ H; simpa using hjH p.1.2)
    have hminus : E.r (f p.1.1) (f (p.1.1 - j p.1.2)) :=
      (hred _ _).mp (by change p.1.1 - (p.1.1 - j p.1.2) ∈ H; simpa using hjH p.1.2)
    have hp' : (f (p.1.1 + j p.1.2), f p.1.1) ∈ ⋃ n, K.piece n := by
      rw [K.iUnion_piece]; exact hplus
    have hm' : (f p.1.1, f (p.1.1 - j p.1.2)) ∈ ⋃ n, K.piece n := by
      rw [K.iUnion_piece]; exact hminus
    obtain ⟨n, hn⟩ := mem_iUnion.mp hp'
    obtain ⟨m, hm⟩ := mem_iUnion.mp hm'
    exact ⟨max n m, K.monotone_piece (le_max_left _ _) hn,
      K.monotone_piece (le_max_right _ _) hm⟩
  obtain ⟨n, p, hpQ⟩ := nonempty_interior_of_iUnion_of_closed hQclosed hQcover
  obtain ⟨W, hW, hWeq⟩ := isOpen_induced_iff.mp (isOpen_interior : IsOpen (interior (Q n)))
  have hpW : p.1 ∈ W := by change p ∈ Subtype.val ⁻¹' W; rwa [hWeq]
  obtain ⟨V, O, hV, hpV, hO, hpO, hVO⟩ := mem_nhds_prod_iff'.mp (hW.mem_nhds hpW)
  have hbound : ∀ q ∈ D ∩ (V ×ˢ O),
      (f (q.1 + j q.2), f q.1) ∈ K.piece n ∧
      (f q.1, f (q.1 - j q.2)) ∈ K.piece n := by
    intro q hq
    change (⟨q, hq.1⟩ : D) ∈ Q n
    apply (interior_subset : interior (Q n) ⊆ Q n)
    rw [← hWeq]
    exact hVO hq.2
  refine ⟨{
    level := n
    base := V
    param := O
    isOpen_base := hV
    isOpen_param := hO
    nonempty_base := ⟨p.1.1, hpV⟩
    nonempty_param := ⟨p.1.2, hpO⟩
    plus := ?_
    minus := ?_ }⟩
  · intro x hx t ht hxC hxtC
    exact closed_edge_extension (p := (x, t)) f hf (fun q : B × P => q.1 + j q.2) Prod.fst
      (continuous_fst.add (hj.comp continuous_snd)) continuous_fst hDd (hV.prod hO)
      (fun q hq => ⟨hq.2.1, hq.1⟩) (K.isClosed_piece n)
      (fun q hq => (hbound q hq).1) ⟨hx, ht⟩ hxtC hxC
  · intro x hx t ht hxC hxtC
    exact closed_edge_extension (p := (x, t)) f hf Prod.fst (fun q : B × P => q.1 - j q.2)
      continuous_fst (continuous_fst.sub (hj.comp continuous_snd)) hDd (hV.prod hO)
      (fun q hq => ⟨hq.1, hq.2.2⟩) (K.isClosed_piece n)
      (fun q hq => (hbound q hq).2) ⟨hx, ht⟩ hxC hxtC

namespace ReductionRectangle

variable {E : EquivRel Y} {K : ClosedExhaustion E} {j : P → B} {f : B → Y} {C : Set B}

def triple (R : ReductionRectangle K j f C) (x : B) (t u : P)
    (hx : x ∈ R.base) (ht : t ∈ R.param) (hu : u ∈ R.param)
    (hxC : x ∈ C) (hpC : x + j t ∈ C) (hmC : x - j u ∈ C) : K.CompositionSpace R.level :=
  ⟨(f (x + j t), f x, f (x - j u)), R.plus x hx t ht hxC hpC, R.minus x hx u hu hxC hmC⟩

end ReductionRectangle

omit [PolishSpace P] [PolishSpace Y] in
/-- Every surviving source pair gives a surviving target triple on the rectangle. -/
theorem compare_remainders {E : EquivRel Y} (K : ClosedExhaustion E)
    (H : AddSubgroup B) (j : P → B) (hj : Continuous j)
    (f : B → Y) (hred : IsReduction (cosetRel H) E f)
    {C : Set B} (hC : C ∈ residual B) (hf : ContinuousOn f C)
    (R : ReductionRectangle K j f C) (a : Ordinal) :
    ∀ t u, (t, u) ∈ escapeRemainder j H a →
      ∀ (ht : t ∈ R.param) (hu : u ∈ R.param), ∀ x,
      ∀ (hx : x ∈ R.base) (hxC : x ∈ C) (hpC : x + j t ∈ C) (hmC : x - j u ∈ C),
        R.triple x t u hx ht hu hxC hpC hmC ∈ K.remainder R.level a := by
  induction a using Ordinal.limitRecOn with
  | zero => simp
  | add_one a ih =>
    intro t u htu ht hu x hx hxC hpC hmC
    have hD : (t, u) ∈ escapeDerivative j H (escapeRemainder j H a) :=
      by simpa only [escapeRemainder_add_one] using htu
    have hold := ih t u (escapeDerivative_subset j H _ hD) ht hu x hx hxC hpC hmC
    by_contra hremoved
    obtain ⟨k, W, hW, hpW, hbound⟩ :=
      K.exists_ambient_open_bound_of_removed R.level a hold hremoved
    obtain ⟨UP, Urest, hUP, hfp, hUrest, hfrest, hUprod⟩ :=
      mem_nhds_prod_iff'.mp (hW.mem_nhds hpW)
    obtain ⟨U₀, UM, hU₀, hf0, hUM, hfm, hUrestprod⟩ :=
      mem_nhds_prod_iff'.mp (hUrest.mem_nhds hfrest)
    obtain ⟨NP, hNP, hxNP, hmapP⟩ := exists_open_source_neighborhood f hf hpC hUP hfp
    obtain ⟨N₀, hN₀, hxN₀, hmap₀⟩ := exists_open_source_neighborhood f hf hxC hU₀ hf0
    obtain ⟨NM, hNM, hxNM, hmapM⟩ := exists_open_source_neighborhood f hf hmC hUM hfm
    obtain ⟨A, U, V, hA, hxA, hU, htU, hV, huV, hshape⟩ :=
      exists_shift_neighborhoods j hj x t u hNP (hN₀.inter R.isOpen_base) hNM
        hxNP ⟨hxN₀, hx⟩ hxNM
    obtain ⟨z, hzH, q, hqR, hqUV, hqlim⟩ := exists_escape_sequence j H hD
      ((hU.inter R.isOpen_param).prod (hV.inter R.isOpen_param)) ⟨⟨htU, ht⟩, huV, hu⟩
    have hseq : ∀ᶠ v in residual B, ∀ l : ℕ,
        v - j (q l).1 ∈ C ∧ v - pairSum j (q l) ∈ C :=
      eventually_countable_forall.mpr fun l =>
        (residual_sub hC (j (q l).1)).and (residual_sub hC (pairSum j (q l)))
    have hall : ∀ᶠ v in residual B, v ∈ C ∧ v - z ∈ C ∧
        ∀ l : ℕ, v - j (q l).1 ∈ C ∧ v - pairSum j (q l) ∈ C := by
      filter_upwards [hC, residual_sub hC z, hseq] with v hv hz hq
      exact ⟨hv, hz, hq⟩
    obtain ⟨v, hvA, hv⟩ := (dense_of_mem_residual hall).inter_open_nonempty A hA ⟨_, hxA⟩
    have hedges : ∀ l : ℕ, (f v, f (v - pairSum j (q l))) ∈ K.piece k := by
      intro l
      have hloc := hshape v hvA (q l).1 (hqUV l).1.1 (q l).2 (hqUV l).2.1
      have hend : v - j (q l).1 - j (q l).2 = v - pairSum j (q l) := by
        dsimp [pairSum]
        abel
      have hpLC : v - j (q l).1 + j (q l).1 ∈ C := by simpa using hv.1
      have hmLC : v - j (q l).1 - j (q l).2 ∈ C := by rw [hend]; exact (hv.2.2 l).2
      let qtarget := R.triple (v - j (q l).1) (q l).1 (q l).2 hloc.2.1.2
        (hqUV l).1.2 (hqUV l).2.2 (hv.2.2 l).1 hpLC hmLC
      have hqt : qtarget ∈ K.remainder R.level a :=
        ih (q l).1 (q l).2 (hqR l) (hqUV l).1.2 (hqUV l).2.2
          (v - j (q l).1) hloc.2.1.2 (hv.2.2 l).1 hpLC hmLC
      have hqtW : qtarget.1 ∈ W := by
        apply hUprod
        refine ⟨?_, hUrestprod ⟨?_, ?_⟩⟩
        · simpa only [qtarget, ReductionRectangle.triple, sub_add_cancel] using hmapP v hloc.1 hv.1
        · exact hmap₀ _ hloc.2.1.1 (hv.2.2 l).1
        · exact hmapM _ hloc.2.2 hmLC
      have hpair := hbound qtarget hqt hqtW
      simpa only [qtarget, ReductionRectangle.triple, sub_add_cancel, hend] using hpair
    have hlast : Tendsto (fun l => f (v - pairSum j (q l))) atTop (𝓝 (f (v - z))) :=
      (hf _ hv.2.1).tendsto.comp (tendsto_nhdsWithin_iff.mpr
        ⟨tendsto_const_nhds.sub hqlim, Eventually.of_forall fun l => (hv.2.2 l).2⟩)
    have hpair : (f v, f (v - z)) ∈ K.piece k :=
      (K.isClosed_piece k).mem_of_tendsto
        (tendsto_const_nhds.prodMk_nhds hlast) (Eventually.of_forall hedges)
    have hzmem : z ∈ H := by
      have hcoset := (hred v (v - z)).mpr (K.piece_subset k hpair)
      change v - (v - z) ∈ H at hcoset
      simpa using hcoset
    exact hzH hzmem
  | limit a ha ih =>
    intro t u htu ht hu x hx hxC hpC hmC
    rw [K.remainder_limit R.level ha]
    rw [escapeRemainder_limit j H ha] at htu
    exact mem_iInter.mpr fun b => ih b.1 b.2 t u (mem_iInter.mp htu b) ht hu x hx hxC hpC hmC

/-- A diagonal surviving through `a` forces a surviving composition triple at some target
level whenever there is a Baire-measurable reduction. -/
theorem exists_nonempty_target_remainder [Nonempty P] {E : EquivRel Y}
    (K : ClosedExhaustion E) (H : AddSubgroup B) (j : P → B)
    (hj : Continuous j) (hjH : ∀ t, j t ∈ H) (a : Ordinal)
    (hdiag : ∀ t, (t, t) ∈ escapeRemainder j H a)
    (hred : BaireReducible (cosetRel H) E) :
    ∃ n, (K.remainder n a).Nonempty := by
  obtain ⟨f, hfB, hred⟩ := hred
  obtain ⟨C, hCG, hC, hf⟩ := exists_Gδ_continuousOn hfB
  obtain ⟨R⟩ := exists_reductionRectangle K H j hj hjH f hred hCG hC hf
  obtain ⟨t, ht⟩ := R.nonempty_param
  have hall : ∀ᶠ x in residual B, x ∈ C ∧ x + j t ∈ C ∧ x - j t ∈ C := by
    filter_upwards [hC, residual_sub hC (-j t), residual_sub hC (j t)] with x hx hp hm
    exact ⟨hx, by simpa only [sub_neg_eq_add] using hp, hm⟩
  obtain ⟨x, hx, hxC, hpC, hmC⟩ :=
    (dense_of_mem_residual hall).inter_open_nonempty R.base R.isOpen_base R.nonempty_base
  exact ⟨R.level, R.triple x t t hx ht ht hxC hpC hmC,
    compare_remainders K H j hj f hred hC hf R a t t (hdiag t) ht ht x hx hxC hpC hmC⟩

/-- The source diagonal rank cannot exceed a common bound for the target derivatives. -/
theorem not_baireReducible_of_diagonal_rank [Nonempty P] {E : EquivRel Y}
    (K : ClosedExhaustion E) (H : AddSubgroup B) (j : P → B)
    (hj : Continuous j) (hjH : ∀ t, j t ∈ H) (a : Ordinal)
    (hdiag : ∀ t, (t, t) ∈ escapeRemainder j H a)
    (hempty : ∀ n, K.remainder n a = ∅) :
    ¬ BaireReducible (cosetRel H) E := by
  intro hred
  obtain ⟨n, p, hp⟩ := exists_nonempty_target_remainder K H j hj hjH a hdiag hred
  rw [hempty n] at hp
  exact hp

end NoUniversalFSigma.Proof
