module

public import NoUniversalFSigma.PacketFeatures
public import NoUniversalFSigma.MixtureCharts

@[expose] public section

/-! Countable data for the closed charts of the countable algebraic tensor span. -/

noncomputable section

namespace NoUniversalFSigma.Proof.Packet

open Set Topology NoUniversalFSigma
open scoped lp

attribute [local instance] Classical.propDecidable

variable (A : ℕ → AdmissibleFamily)

/-- A finite choice of normalized features at coordinates outside the fixed head. -/
abbrev WitnessFeature (B : Finset ℕ) (W : Finset {n // n ∉ B}) :=
  ∀ w : W, (A w.val.val).NormalizedFeature

instance witnessFeatureCountable (B : Finset ℕ) (W : Finset {n // n ∉ B}) :
    Countable (WitnessFeature A B W) := by
  dsimp [WitnessFeature]
  infer_instance

/-- The scalar value of a finite product feature on an outside label. -/
def witnessValue (B : Finset ℕ) (W : Finset {n // n ∉ B})
    (a : WitnessFeature A B W) (q : TailParam A B) : ℝ :=
  ∏ w : W, hilbertFinsuppFunctional ((A w.val.val).normalizedFunctional (a w))
    ((A w.val.val).j (q w.val))

theorem continuous_witnessValue (B : Finset ℕ) (W : Finset {n // n ∉ B})
    (a : WitnessFeature A B W) : Continuous (witnessValue A B W a) := by
  apply continuous_finsetProd
  intro w _
  exact (hilbertFinsuppFunctional ((A w.val.val).normalizedFunctional (a w))).continuous.comp
    ((A w.val.val).continuous_j.comp (continuous_apply w.val))

/-- All choices in a chart range over countable sets; the real-valued constraints occur only
through the fixed, countably indexed normalized features. -/
structure TensorChartIndex where
  B : Finset ℕ
  size : ℕ
  W1 : Finset {n // n ∉ B}
  W2 : Finset {n // n ∉ B}
  disjoint : Disjoint W1 W2
  feature1 : Fin size → WitnessFeature A B W1
  feature2 : Fin size → WitnessFeature A B W2
  piece : Fin size → ℕ
  coord : Fin size → HeadCoord A B
  bound : ℕ
  deriving Countable

instance tensorChartIndexNonempty : Nonempty (TensorChartIndex A) :=
  ⟨{ B := ∅
     size := 0
     W1 := ∅
     W2 := ∅
     disjoint := Finset.disjoint_empty_left _
     feature1 := Fin.elim0
     feature2 := Fin.elim0
     piece := Fin.elim0
     coord := Fin.elim0
     bound := 0 }⟩

/-- Two disjoint finite packets pin each summand independently. -/
def pinSet (d : TensorChartIndex A) : Set (Fin d.size → TailParam A d.B) :=
  {q | ∀ c e,
    witnessValue A d.B d.W1 (d.feature1 c) (q e) = (if c = e then 1 else 0) ∧
    witnessValue A d.B d.W2 (d.feature2 c) (q e) = (if c = e then 1 else 0)}

theorem isClosed_pinSet (d : TensorChartIndex A) : IsClosed (pinSet A d) := by
  simp only [pinSet, ofPred_forall, ofPred_and]
  apply isClosed_iInter
  intro c
  apply isClosed_iInter
  intro e
  apply IsClosed.inter
  · exact isClosed_eq ((continuous_witnessValue A d.B d.W1 (d.feature1 c)).comp
      (continuous_apply e)) continuous_const
  · exact isClosed_eq ((continuous_witnessValue A d.B d.W2 (d.feature2 c)).comp
      (continuous_apply e)) continuous_const

/-- Fix a countable closed cover of each finite packet's algebraic span. -/
def headClosedCover (B : Finset ℕ) : ℕ → Set (HeadSpace A B) :=
  (isSigma02_span_finitePacket A B).choose

theorem isClosed_headClosedCover (B : Finset ℕ) (n : ℕ) :
    IsClosed (headClosedCover A B n) :=
  (isSigma02_span_finitePacket A B).choose_spec.1 n

theorem headSpan_eq_iUnion (B : Finset ℕ) :
    (Submodule.span ℝ (range (finitePacket A B)) : Set (HeadSpace A B)) =
      ⋃ n, headClosedCover A B n := (isSigma02_span_finitePacket A B).choose_spec.2

theorem headClosedCover_subset_span (B : Finset ℕ) (n : ℕ) :
    headClosedCover A B n ⊆ Submodule.span ℝ (range (finitePacket A B)) := by
  rw [headSpan_eq_iUnion]
  exact subset_iUnion _ n

/-- A closed coefficient chart also certifies one nonzero coordinate. -/
def coefficientSet (d : TensorChartIndex A) (c : Fin d.size) : Set (HeadSpace A d.B) :=
  headClosedCover A d.B (d.piece c) ∩ {v | 1 / (d.bound + 1 : ℝ) ≤ |v (d.coord c)|}

theorem isClosed_coefficientSet (d : TensorChartIndex A) (c : Fin d.size) :
    IsClosed (coefficientSet A d c) :=
  (isClosed_headClosedCover A d.B (d.piece c)).inter
    (isClosed_le continuous_const
      ((lp.evalCLM ℝ (fun _ : HeadCoord A d.B => ℝ) 2 (d.coord c)).continuous.abs))

theorem coefficientSet_nonzero (d : TensorChartIndex A) (c : Fin d.size)
    {v : HeadSpace A d.B} (hv : v ∈ coefficientSet A d c) : v (d.coord c) ≠ 0 := by
  apply abs_pos.mp
  exact (by positivity : (0 : ℝ) < 1 / (d.bound + 1 : ℝ)).trans_le hv.2

/-- Each finite family of nonzero coefficients fits closed cover pieces and one common
positive reciprocal bound, with a nonzero coordinate chosen separately for each coefficient. -/
theorem exists_coefficient_data (B : Finset ℕ) {S : Type} [Finite S]
    (v : S → HeadSpace A B)
    (hv : ∀ c, v c ∈ Submodule.span ℝ (range (finitePacket A B)))
    (hnonzero : ∀ c, v c ≠ 0) :
    ∃ (piece : S → ℕ) (coord : S → HeadCoord A B) (k : ℕ),
      ∀ c, v c ∈ headClosedCover A B (piece c) ∧
        1 / (k + 1 : ℝ) ≤ |v c (coord c)| := by
  classical
  let _ : Fintype S := Fintype.ofFinite S
  have hpiece (c : S) : ∃ n, v c ∈ headClosedCover A B n := by
    have h := hv c
    rw [← SetLike.mem_coe, headSpan_eq_iUnion, mem_iUnion] at h
    exact h
  choose piece hpiece using hpiece
  have hcoord (c : S) : ∃ i, v c i ≠ 0 := by
    by_contra h
    push Not at h
    exact hnonzero c (by ext i; exact h i)
  choose coord hcoord using hcoord
  choose k hk using fun c => exists_nat_one_div_lt (abs_pos.mpr (hcoord c))
  let K := Finset.univ.sup k
  refine ⟨piece, coord, K, fun c => ⟨hpiece c, ?_⟩⟩
  apply le_trans _ (hk c).le
  apply one_div_le_one_div_of_le (by positivity)
  have hkc : k c ≤ K := Finset.le_sup (f := k) (Finset.mem_univ c)
  exact_mod_cast Nat.add_le_add_right hkc 1

/-- A closed mixture chart in the ambient completed Hilbert space. -/
def tensorChart (d : TensorChartIndex A) : Set (Space A) :=
  mixtureChart (mix A d.B) (coefficientSet A d) (pinSet A d)

theorem tensorChart_subset_span (d : TensorChartIndex A) : tensorChart A d ⊆ span A := by
  rintro z ⟨v, q, hv, _, rfl⟩
  exact Submodule.sum_mem _ fun c _ => mix_mem_span A d.B
    (headClosedCover_subset_span A d.B (d.piece c) (hv c).1) (q c)

end NoUniversalFSigma.Proof.Packet
