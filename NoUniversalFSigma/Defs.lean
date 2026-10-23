module

public import NoUniversalFSigma.Definitions
public import Mathlib.Topology.Baire.BaireMeasurable

@[expose] public section

/-! Internal definitions for the nonuniversality proof.

Baire measurability uses the Baire property rather than the Baire sigma algebra.
-/

namespace NoUniversalFSigma.Proof

open Set NoUniversalFSigma

variable {X Y : Type*}

/-- The equivalence relation of belonging to the same coset of an additive subgroup. -/
def cosetRel [AddCommGroup X] (H : AddSubgroup X) : EquivRel X where
  r x y := x - y ∈ H
  isEquiv := by
    refine ⟨fun x => by simp, ?_, ?_⟩
    · intro x y h
      simpa only [neg_sub] using H.neg_mem h
    · intro x y z hxy hyz
      simpa only [sub_add_sub_cancel] using H.add_mem hxy hyz

/-- A map is Baire measurable when inverse images of open sets have the Baire property. -/
def IsBaireMeasurable [TopologicalSpace X] [TopologicalSpace Y] (f : X → Y) : Prop :=
  ∀ U : Set Y, IsOpen U → BaireMeasurableSet (f ⁻¹' U)

/-- A Baire-measurable reduction preserves and reflects the equivalence relation. -/
def IsBaireReduction [TopologicalSpace X] [TopologicalSpace Y]
    (E : EquivRel X) (F : EquivRel Y) (f : X → Y) : Prop :=
  IsBaireMeasurable f ∧ IsReduction E F f

/-- Reducibility by a map whose inverse images of open sets have the Baire property. -/
def BaireReducible [TopologicalSpace X] [TopologicalSpace Y]
    (E : EquivRel X) (F : EquivRel Y) : Prop :=
  ∃ f : X → Y, IsBaireReduction E F f

end NoUniversalFSigma.Proof
