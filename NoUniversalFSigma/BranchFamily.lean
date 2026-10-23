module

public import NoUniversalFSigma.BranchSpan
public import NoUniversalFSigma.Admissible

@[expose] public section

/-! # The branch family as the initial admissible family -/

noncomputable section

open Set
open scoped lp

namespace NoUniversalFSigma.Proof.Branch

/-- A finitely supported presentation of one Hilbert coordinate evaluation. -/
def coordinateFunctional (c : Coord) : Coord →₀ ℝ := Finsupp.single c 1

@[simp]
lemma coordinateFunctional_apply (c : Coord) (b : Space) :
    hilbertFinsuppFunctional (coordinateFunctional c) b = b c := by
  simp [coordinateFunctional, hilbertFinsuppFunctional_apply]

/-- A countable enumeration of every marker and signed coordinate. -/
def coordinateEnum : ℕ → Coord := (exists_surjective_nat Coord).choose

lemma coordinateEnum_surjective : Function.Surjective coordinateEnum :=
  (exists_surjective_nat Coord).choose_spec

/-- The initial admissible family: the bounded, closed branch embedding with `Fσ` span. -/
def family : AdmissibleFamily where
  Coord := Coord
  countableCoord := inferInstance
  Param := Point
  topologyParam := inferInstance
  polishParam := inferInstance
  nonemptyParam := inferInstance
  j := j
  closedEmbedding := isClosedEmbedding_j
  bound := 8 / 3
  bound_nonneg := by norm_num
  norm_le := norm_j_le
  mass := coordinateFunctional (nodePrefix (fun _ => 0) 0, none)
  mass_one := by
    intro x
    rw [coordinateFunctional_apply]
    exact j_mass x
  features := fun n => coordinateFunctional (coordinateEnum n)
  features_locallyConstant := by
    intro n
    simpa only [Function.comp_def, coordinateFunctional_apply] using
      isLocallyConstant_coordinate (coordinateEnum n)
  features_separate := by
    intro x y hxy
    obtain ⟨c, hc⟩ : ∃ c : Coord, j x c ≠ j y c := by
      by_contra h
      push Not at h
      exact hxy (coordinates_separate h)
    obtain ⟨n, hn⟩ := coordinateEnum_surjective c
    refine ⟨n, ?_⟩
    simpa only [coordinateFunctional_apply, hn] using hc
  span_isSigma02 := isSigma02_span

end NoUniversalFSigma.Proof.Branch
