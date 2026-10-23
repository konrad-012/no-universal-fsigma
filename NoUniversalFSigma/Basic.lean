module

public import NoUniversalFSigma.Defs
public import NoUniversalFSigma.BorelHierarchy

@[expose] public section

/-! Elementary complexity and category facts for Wang's nonuniversality theorem. -/

namespace NoUniversalFSigma.Proof

open Set Filter Topology TopologicalSpace NoUniversalFSigma

section Cosets

variable {B : Type*} [AddCommGroup B] [TopologicalSpace B] [IsTopologicalAddGroup B]

/-- The coset graph is the inverse image of the subgroup under continuous subtraction. -/
theorem isSigma02_cosetRel (H : AddSubgroup B) (hH : IsSigma02 (H : Set B)) :
    IsSigma02 (cosetRel H).toGraph :=
  BorelHierarchy.isSigma02_preimage (continuous_fst.sub continuous_snd) hH

end Cosets

section Measurability

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]

/-- Borel measurability implies the Baire measurability used in the paper. -/
theorem isBaireMeasurable_of_measurable [MeasurableSpace X] [BorelSpace X]
    [MeasurableSpace Y] [OpensMeasurableSpace Y] {f : X → Y} (hf : Measurable f) :
    IsBaireMeasurable f :=
  fun _ hU => (hf hU.measurableSet).baireMeasurableSet

/-- The stronger Baire nonreducibility conclusion implies Borel nonreducibility. -/
theorem baireReducible_of_borelReducible [MeasurableSpace X] [BorelSpace X]
    [MeasurableSpace Y] [OpensMeasurableSpace Y] {E : EquivRel X} {F : EquivRel Y}
    (h : BorelReducible E F) : BaireReducible E F := by
  obtain ⟨f, hf, hred⟩ := h
  exact ⟨f, isBaireMeasurable_of_measurable hf, hred⟩

/-- A Baire-measurable map is continuous on a comeager `Gδ` subspace.
This is relative continuity on the subspace, not ambient continuity at its points. -/
theorem exists_Gδ_continuousOn [BaireSpace X] [SecondCountableTopology Y] {f : X → Y}
    (hf : IsBaireMeasurable f) :
    ∃ C : Set X, IsGδ C ∧ C ∈ residual X ∧ ContinuousOn f C := by
  have hO : ∀ V : countableBasis Y, ∃ O : Set X, IsOpen O ∧ f ⁻¹' V =ᵇ O := fun V =>
    (hf V (isOpen_of_mem_countableBasis V.2)).residualEq_isOpen
  choose O hOo hOe using hO
  have : Countable (countableBasis Y) := (countable_countableBasis Y).to_subtype
  have hS : ∀ᶠ x in residual X, ∀ V : countableBasis Y, (x ∈ f ⁻¹' V ↔ x ∈ O V) :=
    eventually_countable_forall.2 fun V => eventuallyEqSet_iff.1 (hOe V)
  obtain ⟨C, hCS, hCG, hCd⟩ := mem_residual.1 hS
  refine ⟨C, hCG, residual_of_dense_Gδ hCG hCd, ?_⟩
  rw [continuousOn_iff_continuous_domRestrict, (isBasis_countableBasis Y).continuous_iff]
  intro V hV
  have : C.domRestrict f ⁻¹' V = Subtype.val ⁻¹' O ⟨V, hV⟩ := by
    ext ⟨x, hx⟩
    exact hCS hx ⟨V, hV⟩
  rw [this]
  exact (hOo _).preimage continuous_subtype_val

end Measurability

end NoUniversalFSigma.Proof
