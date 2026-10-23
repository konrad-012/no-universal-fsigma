module

public import NoUniversalFSigma.Basic
public import NoUniversalFSigma.Hilbert

@[expose] public section

/-! Coordinate presentations of the admissible families in Section 7.

We retain finitely supported coordinate presentations of the mass and separating functionals.
This additional internal invariant is satisfied by the branch family and preserved by the
successor and countable tensor constructions.
-/

namespace NoUniversalFSigma.Proof

open Set Topology NoUniversalFSigma
open scoped lp

/-- An admissible family, with countable Hilbert coordinates and finite-coordinate functionals.
The span field always concerns the algebraic real linear span. -/
structure AdmissibleFamily where
  Coord : Type
  [countableCoord : Countable Coord]
  Param : Type
  [topologyParam : TopologicalSpace Param]
  [polishParam : PolishSpace Param]
  [nonemptyParam : Nonempty Param]
  j : Param → ℓ²(Coord, ℝ)
  closedEmbedding : IsClosedEmbedding j
  bound : ℝ
  bound_nonneg : 0 ≤ bound
  norm_le : ∀ p, ‖j p‖ ≤ bound
  mass : Coord →₀ ℝ
  mass_one : ∀ p, hilbertFinsuppFunctional mass (j p) = 1
  features : ℕ → Coord →₀ ℝ
  features_locallyConstant : ∀ n, IsLocallyConstant (hilbertFinsuppFunctional (features n) ∘ j)
  features_separate : ∀ p q, p ≠ q → ∃ n,
    hilbertFinsuppFunctional (features n) (j p) ≠
      hilbertFinsuppFunctional (features n) (j q)
  span_isSigma02 : IsSigma02 (Submodule.span ℝ (range j) : Set ℓ²(Coord, ℝ))

attribute [instance] AdmissibleFamily.countableCoord AdmissibleFamily.topologyParam
  AdmissibleFamily.polishParam AdmissibleFamily.nonemptyParam

namespace AdmissibleFamily

/-- The ambient space has the norm topology, as opposed to a product of coordinate lines. -/
abbrev Space (A : AdmissibleFamily) := ℓ²(A.Coord, ℝ)

/-- The algebraic real span of the family. -/
noncomputable def span (A : AdmissibleFamily) : Submodule ℝ A.Space :=
  Submodule.span ℝ (range A.j)

theorem j_mem_span (A : AdmissibleFamily) (p : A.Param) : A.j p ∈ A.span :=
  Submodule.subset_span ⟨p, rfl⟩

theorem continuous_j (A : AdmissibleFamily) : Continuous A.j := A.closedEmbedding.continuous

theorem isSigma02_span (A : AdmissibleFamily) : IsSigma02 (A.span : Set A.Space) :=
  A.span_isSigma02

end AdmissibleFamily

end NoUniversalFSigma.Proof
