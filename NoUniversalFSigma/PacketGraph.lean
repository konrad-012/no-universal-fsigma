module

public import NoUniversalFSigma.HilbertSum
public import NoUniversalFSigma.BorelHierarchy

@[expose] public section

/-! The one-factor graph used in finite packets, and its algebraic span. -/

namespace NoUniversalFSigma.Proof

open Set Topology NoUniversalFSigma
open scoped lp

variable {I : Type*}

/-- Store a mass coordinate together with a nonzero scaled copy of a Hilbert vector. -/
noncomputable def hilbertGraph (mass : I →₀ ℝ) (β : ℝ) :
    ℓ²(I, ℝ) →L[ℝ] ℓ²(PUnit.{1} ⊕ I, ℝ) :=
  hilbertJoinCLM.comp
    (((hilbertFinsuppFunctional mass).smulRight
      (lp.single (E := fun _ : PUnit.{1} => ℝ) 2 PUnit.unit 1)).prod
      (β • ContinuousLinearMap.id ℝ ℓ²(I, ℝ)))

@[simp]
theorem hilbertGraph_inl (mass : I →₀ ℝ) (β : ℝ) (v : ℓ²(I, ℝ)) (i : PUnit.{1}) :
    hilbertGraph mass β v (.inl i) = hilbertFinsuppFunctional mass v := by
  cases i
  simp [hilbertGraph, hilbertJoinCLM, hilbertJoinVector]

@[simp]
theorem hilbertGraph_inr (mass : I →₀ ℝ) (β : ℝ) (v : ℓ²(I, ℝ)) (i : I) :
    hilbertGraph mass β v (.inr i) = β * v i := rfl

@[simp]
theorem hilbertRight_graph (mass : I →₀ ℝ) (β : ℝ) (v : ℓ²(I, ℝ)) :
    hilbertRight (hilbertGraph mass β v) = β • v := by
  ext i
  rfl

/-- The scaled right projection recovers the vector from its graph. -/
theorem hilbertGraph_leftInverse (mass : I →₀ ℝ) {β : ℝ} (hβ : β ≠ 0) :
    Function.LeftInverse (fun z : ℓ²(PUnit.{1} ⊕ I, ℝ) => β⁻¹ • hilbertRight z)
      (fun v : ℓ²(I, ℝ) => hilbertGraph mass β v) := by
  intro v
  change β⁻¹ • hilbertRight (hilbertGraph mass β v) = v
  rw [hilbertRight_graph, smul_smul, inv_mul_cancel₀ hβ, one_smul]

/-- Nonzero scaling makes the graph a closed linear embedding. -/
theorem isClosedEmbedding_hilbertGraph (mass : I →₀ ℝ) {β : ℝ} (hβ : β ≠ 0) :
    IsClosedEmbedding (hilbertGraph mass β) :=
  (hilbertGraph_leftInverse mass hβ).isClosedEmbedding
    (β⁻¹ • (hilbertRight : ℓ²(PUnit.{1} ⊕ I, ℝ) →L[ℝ] ℓ²(I, ℝ))).continuous
    (hilbertGraph mass β).continuous

/-- Images of `Fσ` sets under closed embeddings are `Fσ`. -/
theorem isSigma02_image_isClosedEmbedding {X Y : Type*}
    [TopologicalSpace X] [TopologicalSpace Y] {f : X → Y}
    (hf : IsClosedEmbedding f) {C : Set X} (hC : IsSigma02 C) :
    IsSigma02 (f '' C) := by
  obtain ⟨C, hC, rfl⟩ := hC
  refine ⟨fun n => f '' C n, fun n => hf.isClosedMap _ (hC n), ?_⟩
  rw [image_iUnion]

/-- Taking a span commutes with the one-factor graph. -/
theorem span_range_hilbertGraph {P : Type*} (mass : I →₀ ℝ) (β : ℝ)
    (u : P → ℓ²(I, ℝ)) :
    (Submodule.span ℝ (range fun p => hilbertGraph mass β (u p)) : Set ℓ²(PUnit.{1} ⊕ I, ℝ)) =
      hilbertGraph mass β '' (Submodule.span ℝ (range u) : Set ℓ²(I, ℝ)) := by
  have h := congrArg (fun H : Submodule ℝ ℓ²(PUnit.{1} ⊕ I, ℝ) => (H : Set ℓ²(PUnit.{1} ⊕ I, ℝ)))
    (Submodule.map_span (hilbertGraph mass β).toLinearMap (range u))
  rw [Submodule.map_coe] at h
  rw [← range_comp] at h
  exact h.symm

/-- The algebraic span of the one-factor packet family is `Fσ`. -/
theorem isSigma02_span_hilbertGraph {P : Type*} (mass : I →₀ ℝ) {β : ℝ}
    (hβ : β ≠ 0) (u : P → ℓ²(I, ℝ))
    (hu : IsSigma02 (Submodule.span ℝ (range u) : Set ℓ²(I, ℝ))) :
    IsSigma02 (Submodule.span ℝ (range fun p => hilbertGraph mass β (u p)) :
      Set ℓ²(PUnit.{1} ⊕ I, ℝ)) := by
  rw [span_range_hilbertGraph]
  exact isSigma02_image_isClosedEmbedding (isClosedEmbedding_hilbertGraph mass hβ) hu

/-- Change the disjoint mass/vector coordinates into optional coordinates. -/
def packetOptionEquiv (I : Type*) : PUnit.{1} ⊕ I ≃ Option I :=
  (Equiv.sumComm PUnit.{1} I).trans (Equiv.optionEquivSumPUnit I).symm

/-- A one-factor packet in optional coordinates: mass at `none`, vector at `some`. -/
noncomputable def hilbertOptionGraph (mass : I →₀ ℝ) (β : ℝ) :
    ℓ²(I, ℝ) →L[ℝ] ℓ²(Option I, ℝ) :=
  (hilbertReindex (packetOptionEquiv I)).toContinuousLinearEquiv.toContinuousLinearMap.comp
    (hilbertGraph mass β)

@[simp]
theorem hilbertOptionGraph_none (mass : I →₀ ℝ) (β : ℝ) (v : ℓ²(I, ℝ)) :
    hilbertOptionGraph mass β v none = hilbertFinsuppFunctional mass v := by
  change hilbertGraph mass β v (.inl PUnit.unit) = _
  exact hilbertGraph_inl mass β v _

@[simp]
theorem hilbertOptionGraph_some (mass : I →₀ ℝ) (β : ℝ) (v : ℓ²(I, ℝ)) (i : I) :
    hilbertOptionGraph mass β v (some i) = β * v i := rfl

theorem isClosedEmbedding_hilbertOptionGraph (mass : I →₀ ℝ) {β : ℝ} (hβ : β ≠ 0) :
    IsClosedEmbedding (hilbertOptionGraph mass β) :=
  (hilbertReindex (packetOptionEquiv I)).toHomeomorph.isClosedEmbedding.comp
    (isClosedEmbedding_hilbertGraph mass hβ)

/-- One-factor packet graph spans are `Fσ` in optional Hilbert coordinates. -/
theorem isSigma02_span_hilbertOptionGraph {P : Type*} (mass : I →₀ ℝ) {β : ℝ}
    (hβ : β ≠ 0) (u : P → ℓ²(I, ℝ))
    (hu : IsSigma02 (Submodule.span ℝ (range u) : Set ℓ²(I, ℝ))) :
    IsSigma02 (Submodule.span ℝ (range fun p => hilbertOptionGraph mass β (u p)) :
      Set ℓ²(Option I, ℝ)) := by
  have h := congrArg (fun H : Submodule ℝ ℓ²(Option I, ℝ) => (H : Set ℓ²(Option I, ℝ)))
    (Submodule.map_span (hilbertOptionGraph mass β).toLinearMap (range u))
  rw [Submodule.map_coe, ← range_comp] at h
  exact h ▸ isSigma02_image_isClosedEmbedding (isClosedEmbedding_hilbertOptionGraph mass hβ) hu

end NoUniversalFSigma.Proof
