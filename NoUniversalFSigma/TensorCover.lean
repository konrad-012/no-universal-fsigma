module

public import NoUniversalFSigma.FiniteMatrix
public import NoUniversalFSigma.BorelHierarchy

@[expose] public section

/-! The countable closed charts used for finite algebraic tensor spans. -/

namespace NoUniversalFSigma.Proof

open Set NoUniversalFSigma

namespace CoordinateMatrix

/-- All data needed to choose one finite-minor chart. -/
structure ChartIndex (I J : Type*) where
  size : ℕ
  rows : Fin size → I
  cols : Fin size → J
  detBound : ℕ
  columnPiece : Fin size → ℕ
  rowPiece : Fin size → ℕ
  deriving Countable

variable {I J U V W : Type*}

/-- A minor chart fixes a nondegenerate maximal minor and closed-cover members for its
selected columns and rows. The positive determinant lower bound makes each chart closed. -/
def minorChart (M : W → Matrix I J ℝ) (column : J → W → U) (row : I → W → V)
    (H : ℕ → Set U) (K : ℕ → Set V) (d : ChartIndex I J) : Set W :=
  {x | RankAtMost d.size (M x) ∧
    1 / (d.detBound + 1 : ℝ) ≤ |((M x).submatrix d.rows d.cols).det| ∧
    (∀ t, column (d.cols t) x ∈ H (d.columnPiece t)) ∧
    (∀ s, row (d.rows s) x ∈ K (d.rowPiece s))}

theorem isClosed_minorChart [TopologicalSpace W] [TopologicalSpace U] [TopologicalSpace V]
    (M : W → Matrix I J ℝ) (column : J → W → U) (row : I → W → V)
    (hM : ∀ i j, Continuous fun x => M x i j)
    (hcolumn : ∀ j, Continuous (column j)) (hrow : ∀ i, Continuous (row i))
    (H : ℕ → Set U) (K : ℕ → Set V)
    (hH : ∀ n, IsClosed (H n)) (hK : ∀ n, IsClosed (K n)) (d : ChartIndex I J) :
    IsClosed (minorChart M column row H K d) := by
  have hdet : Continuous fun x => ((M x).submatrix d.rows d.cols).det :=
    (continuous_pi fun s => continuous_pi fun t => hM (d.rows s) (d.cols t)).matrix_det
  simpa only [minorChart, ofPred_and, ofPred_forall, Set.preimage] using
    (isClosed_rankAtMost d.size M hM).inter
    ((isClosed_le continuous_const hdet.abs).inter
      ((isClosed_iInter fun t : Fin d.size =>
        (hH (d.columnPiece t)).preimage (hcolumn (d.cols t))).inter
        (isClosed_iInter fun s : Fin d.size =>
          (hK (d.rowPiece s)).preimage (hrow (d.rows s)))))

/-- The charts of finite coordinate tensors form an `Fσ` set. -/
theorem isSigma02_iUnion_minorChart [Countable I] [Countable J]
    [TopologicalSpace W] [TopologicalSpace U] [TopologicalSpace V]
    (M : W → Matrix I J ℝ) (column : J → W → U) (row : I → W → V)
    (hM : ∀ i j, Continuous fun x => M x i j)
    (hcolumn : ∀ j, Continuous (column j)) (hrow : ∀ i, Continuous (row i))
    (H : ℕ → Set U) (K : ℕ → Set V)
    (hH : ∀ n, IsClosed (H n)) (hK : ∀ n, IsClosed (K n)) :
    IsSigma02 (⋃ d : ChartIndex I J, minorChart M column row H K d) := by
  classical
  have : Nonempty (ChartIndex I J) :=
    ⟨⟨0, Fin.elim0, Fin.elim0, 0, Fin.elim0, Fin.elim0⟩⟩
  let e : ℕ → ChartIndex I J := (exists_surjective_nat (ChartIndex I J)).choose
  have he : Function.Surjective e := (exists_surjective_nat (ChartIndex I J)).choose_spec
  refine ⟨fun n => minorChart M column row H K (e n),
    fun n => isClosed_minorChart M column row hM hcolumn hrow H K hH hK (e n), ?_⟩
  exact (Function.Surjective.iUnion_comp he _).symm

/-- Every finite-rank matrix whose rows and columns belong to the prescribed covered
subspaces lies in a chart. Selection of the nonzero minor and all cover indices is finite. -/
theorem mem_iUnion_minorChart_of_finiteRank
    (M : W → Matrix I J ℝ) (column : J → W → U) (row : I → W → V)
    (H : ℕ → Set U) (K : ℕ → Set V) (x : W)
    (hfinite : ∃ r, RankAtMost r (M x))
    (hcolumn : ∀ j, column j x ∈ ⋃ a, H a)
    (hrow : ∀ i, row i x ∈ ⋃ b, K b) :
    x ∈ ⋃ d : ChartIndex I J, minorChart M column row H K d := by
  classical
  apply mem_iUnion.mpr
  rcases exists_maximal_minor (M x) hfinite with hzero | ⟨r, _hr, hrank, rows, cols, hdet⟩
  · refine ⟨⟨0, Fin.elim0, Fin.elim0, 0, Fin.elim0, Fin.elim0⟩, ?_⟩
    simp [minorChart, RankAtMost, hzero, Matrix.det_fin_zero]
  · choose a ha using fun t : Fin r => mem_iUnion.mp (hcolumn (cols t))
    choose b hb using fun s : Fin r => mem_iUnion.mp (hrow (rows s))
    obtain ⟨k, hk⟩ := exists_nat_one_div_lt (abs_pos.mpr hdet)
    exact ⟨⟨r, rows, cols, k, a, b⟩, hrank, hk.le, ha, hb⟩

end CoordinateMatrix

end NoUniversalFSigma.Proof
