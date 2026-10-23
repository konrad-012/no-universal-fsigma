module

public import NoUniversalFSigma.Admissible
public import NoUniversalFSigma.HilbertSum
public import NoUniversalFSigma.Escape

@[expose] public section

/-! The successor operation on admissible families (Section 7.2). -/

namespace NoUniversalFSigma.Proof

open Set Filter Topology NoUniversalFSigma
open scoped lp

namespace AdmissibleFamily

/-- The product family in disjoint Hilbert coordinates. -/
noncomputable def successorJ (A B : AdmissibleFamily) (p : A.Param × B.Param) :
    ℓ²(A.Coord ⊕ B.Coord, ℝ) := hilbertJoin (A.j p.1, B.j p.2)

@[simp] theorem left_successorJ (A B : AdmissibleFamily) (p : A.Param × B.Param) :
    hilbertLeft (successorJ A B p) = A.j p.1 := hilbertLeft_join _

@[simp] theorem right_successorJ (A B : AdmissibleFamily) (p : A.Param × B.Param) :
    hilbertRight (successorJ A B p) = B.j p.2 := hilbertRight_join _

/-- Membership in the two spans with the same total mass. -/
noncomputable def massMatched (A B : AdmissibleFamily) :
    Submodule ℝ ℓ²(A.Coord ⊕ B.Coord, ℝ) where
  carrier := {z | hilbertLeft z ∈ A.span ∧ hilbertRight z ∈ B.span ∧
    hilbertFinsuppFunctional A.mass (hilbertLeft z) =
      hilbertFinsuppFunctional B.mass (hilbertRight z)}
  zero_mem' := by simp
  add_mem' := by
    intro x y hx hy
    exact ⟨by simpa using A.span.add_mem hx.1 hy.1,
      by simpa using B.span.add_mem hx.2.1 hy.2.1,
      by simpa only [map_add] using congrArg₂ (· + ·) hx.2.2 hy.2.2⟩
  smul_mem' := by
    intro c x hx
    exact ⟨by simpa using A.span.smul_mem c hx.1,
      by simpa using B.span.smul_mem c hx.2.1,
      by simpa only [map_smul] using congrArg (c • ·) hx.2.2⟩

@[simp] theorem mem_massMatched (A B : AdmissibleFamily)
    (z : ℓ²(A.Coord ⊕ B.Coord, ℝ)) : z ∈ massMatched A B ↔
      hilbertLeft z ∈ A.span ∧ hilbertRight z ∈ B.span ∧
        hilbertFinsuppFunctional A.mass (hilbertLeft z) =
          hilbertFinsuppFunctional B.mass (hilbertRight z) := Iff.rfl

private noncomputable def leftAnchor (A B : AdmissibleFamily) (s : B.Param) :
    A.Space →L[ℝ] ℓ²(A.Coord ⊕ B.Coord, ℝ) :=
  hilbertJoin.toContinuousLinearMap.comp
    ((ContinuousLinearMap.id ℝ A.Space).prod
      ((hilbertFinsuppFunctional A.mass).smulRight (B.j s)))

private noncomputable def rightAnchor (A B : AdmissibleFamily) (t : A.Param) :
    B.Space →L[ℝ] ℓ²(A.Coord ⊕ B.Coord, ℝ) :=
  hilbertJoin.toContinuousLinearMap.comp
    (((hilbertFinsuppFunctional B.mass).smulRight (A.j t)).prod
      (ContinuousLinearMap.id ℝ B.Space))

/-- The algebraic span consists exactly of the mass-matched pairs. -/
theorem span_successorJ (A B : AdmissibleFamily) :
    Submodule.span ℝ (range (successorJ A B)) = massMatched A B := by
  classical
  let S := Submodule.span ℝ (range (successorJ A B))
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro z ⟨p, rfl⟩
    apply (mem_massMatched A B _).mpr
    exact ⟨by simpa only [left_successorJ] using A.j_mem_span p.1,
      by simpa only [right_successorJ] using B.j_mem_span p.2,
      by rw [left_successorJ, right_successorJ, A.mass_one, B.mass_one]⟩
  · intro z hz
    obtain ⟨hzA, hzB, hmass⟩ := (mem_massMatched A B z).mp hz
    let t : A.Param := Classical.choice inferInstance
    let s : B.Param := Classical.choice inferInstance
    have hL : ∀ v ∈ A.span, leftAnchor A B s v ∈ S := by
      intro v hv
      induction hv using Submodule.span_induction with
      | mem v hv =>
        obtain ⟨p, rfl⟩ := hv
        have heq : leftAnchor A B s (A.j p) = successorJ A B (p, s) := by
          simp [leftAnchor, successorJ, A.mass_one]
        rw [heq]
        exact Submodule.subset_span ⟨(p, s), rfl⟩
      | zero => simp
      | add x y hx hy ihx ihy => simpa only [map_add] using S.add_mem ihx ihy
      | smul c x hx ih => simpa only [map_smul] using S.smul_mem c ih
    have hR : ∀ w ∈ B.span, rightAnchor A B t w ∈ S := by
      intro w hw
      induction hw using Submodule.span_induction with
      | mem w hw =>
        obtain ⟨p, rfl⟩ := hw
        have heq : rightAnchor A B t (B.j p) = successorJ A B (t, p) := by
          simp [rightAnchor, successorJ, B.mass_one]
        rw [heq]
        exact Submodule.subset_span ⟨(t, p), rfl⟩
      | zero => simp
      | add x y hx hy ihx ihy => simpa only [map_add] using S.add_mem ihx ihy
      | smul c x hx ih => simpa only [map_smul] using S.smul_mem c ih
    have hbase : successorJ A B (t, s) ∈ S := Submodule.subset_span ⟨(t, s), rfl⟩
    have hcomb := S.sub_mem (S.add_mem (hL _ hzA) (hR _ hzB))
      (S.smul_mem (hilbertFinsuppFunctional A.mass (hilbertLeft z)) hbase)
    convert hcomb using 1
    ext c
    cases c with
    | inl i =>
      change z (.inl i) = z (.inl i) +
        hilbertFinsuppFunctional B.mass (hilbertRight z) * A.j t i -
        hilbertFinsuppFunctional A.mass (hilbertLeft z) * A.j t i
      rw [← hmass]
      ring
    | inr j =>
      change z (.inr j) = hilbertFinsuppFunctional A.mass (hilbertLeft z) * B.j s j +
        z (.inr j) - hilbertFinsuppFunctional A.mass (hilbertLeft z) * B.j s j
      ring

theorem isSigma02_span_successorJ (A B : AdmissibleFamily) :
    IsSigma02 (Submodule.span ℝ (range (successorJ A B)) : Set ℓ²(A.Coord ⊕ B.Coord, ℝ)) := by
  rw [span_successorJ]
  have hmass : IsClosed {z : ℓ²(A.Coord ⊕ B.Coord, ℝ) |
      hilbertFinsuppFunctional A.mass (hilbertLeft z) =
        hilbertFinsuppFunctional B.mass (hilbertRight z)} :=
    isClosed_eq ((hilbertFinsuppFunctional A.mass).continuous.comp hilbertLeft.continuous)
      ((hilbertFinsuppFunctional B.mass).continuous.comp hilbertRight.continuous)
  have hm : IsSigma02 {z : ℓ²(A.Coord ⊕ B.Coord, ℝ) |
      hilbertFinsuppFunctional A.mass (hilbertLeft z) =
        hilbertFinsuppFunctional B.mass (hilbertRight z)} :=
    ⟨fun _ => _, fun _ => hmass, (iUnion_const _).symm⟩
  exact BorelHierarchy.isSigma02_inter
    (BorelHierarchy.isSigma02_preimage hilbertLeft.continuous A.isSigma02_span)
    (BorelHierarchy.isSigma02_inter
      (BorelHierarchy.isSigma02_preimage hilbertRight.continuous B.isSigma02_span) hm)

/-- Enumerate the finite-coordinate features from the two component families. -/
noncomputable def successorFeatures (A B : AdmissibleFamily) (n : ℕ) :
    A.Coord ⊕ B.Coord →₀ ℝ :=
  match Encodable.decode (α := ℕ ⊕ ℕ) n with
  | none => 0
  | some (.inl k) => (A.features k).sumElim 0
  | some (.inr k) => Finsupp.sumElim 0 (B.features k)

theorem successorFeatures_locallyConstant (A B : AdmissibleFamily) (n : ℕ) :
    IsLocallyConstant (hilbertFinsuppFunctional (successorFeatures A B n) ∘ successorJ A B) := by
  unfold successorFeatures
  cases hd : Encodable.decode (α := ℕ ⊕ ℕ) n with
  | none => simpa [hilbertFinsuppFunctional] using
      (IsLocallyConstant.const (X := A.Param × B.Param) (0 : ℝ))
  | some k =>
    cases k with
    | inl k =>
      simpa only [Function.comp_def, hilbertFinsuppFunctional_sumElim_left,
        hilbertFinsuppFunctional_sumElim_right, left_successorJ, right_successorJ] using
        (A.features_locallyConstant k).comp_continuous
          (continuous_fst : Continuous (Prod.fst : A.Param × B.Param → A.Param))
    | inr k =>
      simpa only [Function.comp_def, hilbertFinsuppFunctional_sumElim_left,
        hilbertFinsuppFunctional_sumElim_right, left_successorJ, right_successorJ] using
        (B.features_locallyConstant k).comp_continuous
          (continuous_snd : Continuous (Prod.snd : A.Param × B.Param → B.Param))

theorem successorFeatures_separate (A B : AdmissibleFamily)
    (p q : A.Param × B.Param) (hpq : p ≠ q) : ∃ n,
      hilbertFinsuppFunctional (successorFeatures A B n) (successorJ A B p) ≠
        hilbertFinsuppFunctional (successorFeatures A B n) (successorJ A B q) := by
  by_cases h : p.1 = q.1
  · have h' : p.2 ≠ q.2 := fun h2 => hpq (Prod.ext h h2)
    obtain ⟨k, hk⟩ := B.features_separate p.2 q.2 h'
    refine ⟨Encodable.encode (Sum.inr k : ℕ ⊕ ℕ), ?_⟩
    unfold successorFeatures
    rw [Encodable.encodek]
    simpa only [hilbertFinsuppFunctional_sumElim_right, right_successorJ] using hk
  · obtain ⟨k, hk⟩ := A.features_separate p.1 q.1 h
    refine ⟨Encodable.encode (Sum.inl k : ℕ ⊕ ℕ), ?_⟩
    unfold successorFeatures
    rw [Encodable.encodek]
    simpa only [hilbertFinsuppFunctional_sumElim_left, left_successorJ] using hk

/-- The successor construction combines two admissible families with matched masses. -/
noncomputable def successor (A B : AdmissibleFamily) : AdmissibleFamily where
  Coord := A.Coord ⊕ B.Coord
  Param := A.Param × B.Param
  j := successorJ A B
  closedEmbedding := hilbertJoin.toHomeomorph.isClosedEmbedding.comp
    (A.closedEmbedding.prodMap B.closedEmbedding)
  bound := A.bound + B.bound
  bound_nonneg := add_nonneg A.bound_nonneg B.bound_nonneg
  norm_le := fun p => (norm_hilbertJoinVector_le _ _).trans
    (add_le_add (A.norm_le p.1) (B.norm_le p.2))
  mass := A.mass.sumElim 0
  mass_one := by
    intro p
    rw [hilbertFinsuppFunctional_sumElim_left, left_successorJ]
    exact A.mass_one p.1
  features := successorFeatures A B
  features_locallyConstant := successorFeatures_locallyConstant A B
  features_separate := successorFeatures_separate A B
  span_isSigma02 := isSigma02_span_successorJ A B

@[simp] theorem successor_j (A B : AdmissibleFamily) : (successor A B).j = successorJ A B := rfl

@[simp] theorem successor_span (A B : AdmissibleFamily) :
    (successor A B).span = massMatched A B := span_successorJ A B

/-- Pair sums split into the two disjoint coordinate families. -/
theorem pairSum_successorJ (A B : AdmissibleFamily) (p q : A.Param × B.Param) :
    pairSum (successorJ A B) (p, q) =
      hilbertJoin (pairSum A.j (p.1, q.1), pairSum B.j (p.2, q.2)) := by
  change hilbertJoin (A.j p.1, B.j p.2) + hilbertJoin (A.j q.1, B.j q.2) = _
  rw [← map_add]
  rfl

/-- Fixed choices in the second factor transfer every stage of the first-factor remainder. -/
theorem successor_transfer_left (A B : AdmissibleFamily) (s r : B.Param) (α : Ordinal) :
    ∀ p ∈ escapeRemainder A.j A.span.toAddSubgroup α,
      ((p.1, s), (p.2, r)) ∈ escapeRemainder
        (successor A B).j (successor A B).span.toAddSubgroup α := by
  apply escapeRemainder_transfer A.j A.span.toAddSubgroup
    (successor A B).j (successor A B).span.toAddSubgroup
    (fun t => (t, s)) (fun t => (t, r))
    (continuous_id.prodMk continuous_const) (continuous_id.prodMk continuous_const)
    (fun v => hilbertJoin (v, B.j s + B.j r))
    (hilbertJoin.continuous.comp (continuous_id.prodMk continuous_const))
  · intro t u
    exact pairSum_successorJ A B (t, s) (u, r)
  · intro z hz hmem
    have hleft : hilbertLeft (hilbertJoin (z, B.j s + B.j r)) ∈ A.span := by
      exact ((mem_massMatched A B _).mp ((successor_span A B) ▸ hmem)).1
    exact hz (A.span.mem_toAddSubgroup.mpr (by
      simpa only [hilbertLeft_join] using hleft))

/-- A family of diagonal rank `α`, combined with one of rank one, has rank `α + 1`. -/
theorem successor_diagonal_rank (A B : AdmissibleFamily) (α : Ordinal)
    (hA : ∀ t, (t, t) ∈ escapeRemainder A.j A.span.toAddSubgroup α)
    (hB : ∀ s, (s, s) ∈ escapeRemainder B.j B.span.toAddSubgroup 1) :
    ∀ p, (p, p) ∈ escapeRemainder
      (successor A B).j (successor A B).span.toAddSubgroup (α + 1) := by
  rintro ⟨t, s⟩
  rw [escapeRemainder_add_one, mem_escapeDerivative_iff]
  refine ⟨successor_transfer_left A B s s α (t, t) (hA t), ?_⟩
  intro U hU hdiag hbound
  let g : B.Param × B.Param → (A.Param × B.Param) × (A.Param × B.Param) :=
    fun q => ((t, q.1), (t, q.2))
  have hg : Continuous g :=
    (continuous_const.prodMk continuous_fst).prodMk
      (continuous_const.prodMk continuous_snd)
  have hB' : (s, s) ∈ escapeDerivative B.j B.span.toAddSubgroup univ := by
    have h := hB s
    rw [show (1 : Ordinal) = 0 + 1 by simp, escapeRemainder_add_one,
      escapeRemainder_zero] at h
    exact h
  obtain ⟨z, hz, q, _hqR, hqU, hqLim⟩ :=
    exists_escape_sequence B.j B.span.toAddSubgroup hB' (hU.preimage hg) hdiag
  have hnot : hilbertJoin (A.j t + A.j t, z) ∉ (successor A B).span.toAddSubgroup := by
    intro hmem
    have hright : hilbertRight (hilbertJoin (A.j t + A.j t, z)) ∈ B.span :=
      ((mem_massMatched A B _).mp ((successor_span A B) ▸ hmem)).2.1
    exact hz (B.span.mem_toAddSubgroup.mpr (by
      simpa only [hilbertRight_join] using hright))
  apply hnot
  apply hbound
  have hL : Continuous (fun w : B.Space => hilbertJoin (A.j t + A.j t, w)) :=
    hilbertJoin.continuous.comp (continuous_const.prodMk continuous_id)
  have hlim : Tendsto (fun l => pairSum (successor A B).j (g (q l))) atTop
      (𝓝 (hilbertJoin (A.j t + A.j t, z))) := by
    change Tendsto (fun l => pairSum (successorJ A B)
      ((t, (q l).1), (t, (q l).2))) atTop _
    simp_rw [pairSum_successorJ]
    exact (hL.tendsto z).comp hqLim
  apply mem_closure_of_tendsto hlim
  exact Eventually.of_forall fun l => ⟨g (q l),
    ⟨successor_transfer_left A B (q l).1 (q l).2 α (t, t) (hA t), hqU l⟩, rfl⟩

end AdmissibleFamily

end NoUniversalFSigma.Proof
