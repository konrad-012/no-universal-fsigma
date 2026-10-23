module

public import NoUniversalFSigma.Rank
public import NoUniversalFSigma.Definitions

@[expose] public section

/-! Composition ranks attached to a fixed closed exhaustion of an equivalence relation. -/

namespace NoUniversalFSigma.Proof

open Set Topology TopologicalSpace NoUniversalFSigma
open scoped Ordinal

universe u

variable {Y : Type u} [TopologicalSpace Y]

/-- A normalized closed exhaustion of an equivalence relation. -/
structure ClosedExhaustion (E : EquivRel Y) where
  piece : ℕ → Set (Y × Y)
  isClosed_piece : ∀ n, IsClosed (piece n)
  monotone_piece : Monotone piece
  refl_piece : ∀ n y, (y, y) ∈ piece n
  symm_piece : ∀ n a b, (a, b) ∈ piece n → (b, a) ∈ piece n
  iUnion_piece : ⋃ n, piece n = E.toGraph

/-- Add the diagonal and the converses of a finite initial segment of a closed cover. -/
def normalizedPiece (C : ℕ → Set (Y × Y)) (n : ℕ) : Set (Y × Y) :=
  {p | p.1 = p.2} ∪ ⋃ i : Fin (n + 1), C i ∪ Prod.swap ⁻¹' C i

theorem exists_closedExhaustion [T2Space Y] (E : EquivRel Y)
    (hE : IsSigma02 E.toGraph) : Nonempty (ClosedExhaustion E) := by
  obtain ⟨C, hC, hcover⟩ := hE
  have hsub (n : ℕ) : C n ⊆ E.toGraph := by
    rw [hcover]
    exact subset_iUnion C n
  refine ⟨{
    piece := normalizedPiece C
    isClosed_piece := fun n => ?_
    monotone_piece := ?_
    refl_piece := fun n y => Or.inl rfl
    symm_piece := ?_
    iUnion_piece := ?_ }⟩
  · exact (isClosed_eq continuous_fst continuous_snd).union
      (isClosed_iUnion_of_finite fun i : Fin (n + 1) =>
        (hC i).union ((hC i).preimage continuous_swap))
  · intro m n hmn p hp
    rcases hp with hp | hp
    · exact Or.inl hp
    · obtain ⟨i, hi⟩ := mem_iUnion.mp hp
      exact Or.inr (mem_iUnion.mpr
        ⟨⟨i.1, lt_of_lt_of_le i.2 (Nat.add_le_add_right hmn 1)⟩, hi⟩)
  · intro n a b hab
    rcases hab with hab | hab
    · exact Or.inl hab.symm
    · obtain ⟨i, hi⟩ := mem_iUnion.mp hab
      exact Or.inr (mem_iUnion.mpr ⟨i, hi.symm⟩)
  · ext p
    simp only [mem_iUnion]
    constructor
    · rintro ⟨n, hn⟩
      rcases hn with hn | hn
      · change E.r p.1 p.2
        rw [hn]
        exact E.isEquiv.refl _
      · obtain ⟨i, hi⟩ := mem_iUnion.mp hn
        rcases hi with hi | hi
        · exact hsub i hi
        · exact E.isEquiv.symm (hsub i hi)
    · intro hp
      rw [hcover] at hp
      obtain ⟨n, hn⟩ := mem_iUnion.mp hp
      exact ⟨n, Or.inr (mem_iUnion.mpr
        ⟨⟨n, Nat.lt_succ_self n⟩, Or.inl hn⟩)⟩

namespace ClosedExhaustion

variable {E : EquivRel Y} (K : ClosedExhaustion E)

theorem piece_subset (n : ℕ) : K.piece n ⊆ E.toGraph := by
  rw [← K.iUnion_piece]
  exact subset_iUnion K.piece n

/-- Triples whose two consecutive edges lie in the fixed level `n`. -/
abbrev CompositionSpace (n : ℕ) :=
  {p : Y × Y × Y // (p.1, p.2.1) ∈ K.piece n ∧ (p.2.1, p.2.2) ∈ K.piece n}

theorem isClosed_compositionSpace (n : ℕ) :
    IsClosed {p : Y × Y × Y |
      (p.1, p.2.1) ∈ K.piece n ∧ (p.2.1, p.2.2) ∈ K.piece n} :=
  ((K.isClosed_piece n).preimage
    (continuous_fst.prodMk (continuous_fst.comp continuous_snd))).inter
      ((K.isClosed_piece n).preimage
        ((continuous_fst.comp continuous_snd).prodMk (continuous_snd.comp continuous_snd)))

instance [PolishSpace Y] (n : ℕ) : PolishSpace (K.CompositionSpace n) :=
  (K.isClosed_compositionSpace n).polishSpace

/-- The closed sublevel sets of the least level needed for the composed edge. -/
def compositionSublevel (n k : ℕ) : Set (K.CompositionSpace n) :=
  {p | (p.1.1, p.1.2.2) ∈ K.piece k}

theorem isClosed_compositionSublevel (n k : ℕ) : IsClosed (K.compositionSublevel n k) :=
  (K.isClosed_piece k).preimage
    ((continuous_fst.comp continuous_subtype_val).prodMk
      (continuous_snd.comp (continuous_snd.comp continuous_subtype_val)))

theorem iUnion_compositionSublevel (n : ℕ) : ⋃ k, K.compositionSublevel n k = univ := by
  ext p
  simp only [mem_iUnion, mem_univ, iff_true]
  have hab : E.r p.1.1 p.1.2.1 := K.piece_subset n p.2.1
  have hbc : E.r p.1.2.1 p.1.2.2 := K.piece_subset n p.2.2
  have hac : (p.1.1, p.1.2.2) ∈ E.toGraph := E.isEquiv.trans hab hbc
  rw [← K.iUnion_piece] at hac
  obtain ⟨k, hk⟩ := mem_iUnion.mp hac
  exact ⟨k, hk⟩

/-- The composition derivative, iterated from all triples at level `n`. -/
def remainder (n : ℕ) : Ordinal.{u} → Set (K.CompositionSpace n) :=
  coverRemainder (K.compositionSublevel n) univ

@[simp] theorem remainder_zero (n : ℕ) : K.remainder n 0 = univ :=
  coverRemainder_zero _ _

@[simp] theorem remainder_add_one (n : ℕ) (a : Ordinal.{u}) :
    K.remainder n (a + 1) = coverDerivative (K.compositionSublevel n) (K.remainder n a) :=
  coverRemainder_add_one _ _ _

theorem remainder_limit (n : ℕ) {a : Ordinal.{u}} (ha : Order.IsSuccLimit a) :
    K.remainder n a = ⋂ b : Iio a, K.remainder n b.1 :=
  coverRemainder_limit _ _ ha

theorem remainder_antitone (n : ℕ) : Antitone (K.remainder n) :=
  coverRemainder_antitone _ _

theorem isClosed_remainder (n : ℕ) (a : Ordinal.{u}) : IsClosed (K.remainder n a) :=
  isClosed_coverRemainder _ isClosed_univ _

theorem exists_open_bound_of_removed (n : ℕ) (a : Ordinal.{u})
    {p : K.CompositionSpace n} (hp : p ∈ K.remainder n a)
    (hremoved : p ∉ K.remainder n (a + 1)) :
    ∃ k, ∃ U : Set (K.CompositionSpace n), IsOpen U ∧ p ∈ U ∧
      K.remainder n a ∩ U ⊆ K.compositionSublevel n k :=
  (not_mem_coverDerivative_iff _ hp).mp (by simpa only [remainder_add_one] using hremoved)

/-- The relative neighborhood in the removal criterion can be taken from the ambient
triple space. -/
theorem exists_ambient_open_bound_of_removed (n : ℕ) (a : Ordinal.{u})
    {p : K.CompositionSpace n} (hp : p ∈ K.remainder n a)
    (hremoved : p ∉ K.remainder n (a + 1)) :
    ∃ k, ∃ W : Set (Y × Y × Y), IsOpen W ∧ p.1 ∈ W ∧
      ∀ q ∈ K.remainder n a, q.1 ∈ W → (q.1.1, q.1.2.2) ∈ K.piece k := by
  obtain ⟨k, U, hU, hpU, hbound⟩ := K.exists_open_bound_of_removed n a hp hremoved
  obtain ⟨W, hW, hWeq⟩ := isOpen_induced_iff.mp hU
  refine ⟨k, W, hW, ?_, fun q hq hqW => ?_⟩
  · change p ∈ Subtype.val ⁻¹' W
    rwa [hWeq]
  · apply hbound ⟨hq, ?_⟩
    rw [← hWeq]
    exact hqW

theorem exists_countable_empty [PolishSpace Y] (n : ℕ) :
    ∃ a < Ordinal.omega 1, K.remainder n a = ∅ :=
  exists_countable_coverRemainder_empty _ (K.isClosed_compositionSublevel n)
    (K.iUnion_compositionSublevel n) isClosed_univ

/-- A single countable bound kills every level of the fixed target exhaustion. -/
theorem exists_countable_common_bound [PolishSpace Y] :
    ∃ a < Ordinal.omega 1, ∀ n, K.remainder n a = ∅ := by
  choose r hr hempty using K.exists_countable_empty
  let a : Ordinal.{u} := ⨆ n, r n
  refine ⟨a, Ordinal.iSup_lt_omega_one hr, fun n => ?_⟩
  apply subset_empty_iff.mp
  rw [← hempty n]
  exact K.remainder_antitone n (Ordinal.le_iSup r n)

theorem exists_positive_countable_common_bound [PolishSpace Y] [Nonempty Y] :
    ∃ a, 0 < a ∧ a < Ordinal.omega 1 ∧ ∀ n, K.remainder n a = ∅ := by
  obtain ⟨a, ha, hempty⟩ := K.exists_countable_common_bound
  refine ⟨a, ?_, ha, hempty⟩
  apply bot_lt_iff_ne_bot.mpr
  intro hzero
  obtain ⟨y⟩ := ‹Nonempty Y›
  have hp : (⟨(y, y, y), K.refl_piece 0 y, K.refl_piece 0 y⟩ : K.CompositionSpace 0)
      ∈ K.remainder 0 a := by simp [hzero]
  rw [hempty 0] at hp
  exact hp

end ClosedExhaustion

/-- Every `Fσ` equivalence relation admits a normalized closed cover and a common countable
termination bound for its composition remainders. -/
theorem exists_exhaustion_countable_bound [PolishSpace Y] (E : EquivRel Y)
    (hE : IsSigma02 E.toGraph) :
    ∃ K : ClosedExhaustion E, ∃ a < Ordinal.omega 1, ∀ n, K.remainder n a = ∅ := by
  obtain ⟨K⟩ := exists_closedExhaustion E hE
  exact ⟨K, K.exists_countable_common_bound⟩

end NoUniversalFSigma.Proof
