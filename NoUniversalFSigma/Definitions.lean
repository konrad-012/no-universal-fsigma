module

public import Mathlib.MeasureTheory.Constructions.Polish.Basic

/-! Definitions appearing in the nonuniversality theorem. -/

@[expose] public section

namespace NoUniversalFSigma

variable {X : Type*} [TopologicalSpace X]

/-- The closed sets. -/
def IsPi01 (s : Set X) : Prop := IsClosed s

/-- The countable unions of closed sets. -/
def IsSigma02 (s : Set X) : Prop :=
  ∃ f : ℕ → Set X, (∀ n, IsPi01 (f n)) ∧ s = ⋃ n, f n

/-- A relation that is reflexive, symmetric, and transitive. -/
structure EquivRel (X : Type*) where
  r : X → X → Prop
  isEquiv : Equivalence r

/-- The pairs of points related by `E`, as a subset of the product space. -/
def EquivRel.toGraph (E : EquivRel X) : Set (X × X) :=
  { p | E.r p.1 p.2 }

variable {Y : Type*}

/-- A reduction preserves and reflects the equivalence relation. -/
def IsReduction (E : EquivRel X) (F : EquivRel Y) (f : X → Y) : Prop :=
  ∀ x₁ x₂ : X, E.r x₁ x₂ ↔ F.r (f x₁) (f x₂)

/-- A measurable reduction for the specified measurable structures. -/
def IsBorelReduction [MeasurableSpace X] [MeasurableSpace Y]
    (E : EquivRel X) (F : EquivRel Y) (f : X → Y) : Prop :=
  Measurable f ∧ IsReduction E F f

/-- There exists a measurable reduction from `E` to `F`. -/
def BorelReducible [MeasurableSpace X] [MeasurableSpace Y]
    (E : EquivRel X) (F : EquivRel Y) : Prop :=
  ∃ f : X → Y, IsBorelReduction E F f

end NoUniversalFSigma
