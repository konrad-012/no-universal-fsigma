module

public import NoUniversalFSigma.PacketCharts
public import NoUniversalFSigma.PacketCover

@[expose] public section

/-! The algebraic span of the countable tensor family is `Fσ` (Wang, Lemma 6.2). -/

noncomputable section

namespace NoUniversalFSigma.Proof.Packet

open Set Topology NoUniversalFSigma
open scoped lp

variable (A : ℕ → AdmissibleFamily)

/-- Regroup by finite differences, select two disjoint pinning packets, and bound finitely
many nonzero coordinate evaluations. These choices put every algebraic span vector in a chart. -/
theorem span_subset_iUnion_tensorChart :
    (span A : Set (Space A)) ⊆ ⋃ d : TensorChartIndex A, tensorChart A d := by
  intro z hz
  obtain ⟨B, m, v, p, hv, hne, hsep, hsum⟩ := exists_reduced_mixture A hz
  obtain ⟨W1, W2, hW, a1, a2, ha⟩ := exists_disjoint_delta_features A B m p hsep
  obtain ⟨piece, coord, k, hcoeff⟩ := exists_coefficient_data A B v hv hne
  let d : TensorChartIndex A :=
    { B := B
      size := m
      W1 := W1
      W2 := W2
      disjoint := hW
      feature1 := a1
      feature2 := a2
      piece := piece
      coord := coord
      bound := k }
  apply mem_iUnion.mpr
  refine ⟨d, v, fun c => restrictParam A B (p c), ?_, ?_, hsum⟩
  · exact hcoeff
  · exact ha

/-- The constructed countable family has an `Fσ` algebraic real span in its norm Hilbert space. -/
theorem isSigma02_span : IsSigma02 (span A : Set (Space A)) := by
  have heq : (span A : Set (Space A)) =
      ⋃ d : TensorChartIndex A, tensorChart A d := by
    apply subset_antisymm (span_subset_iUnion_tensorChart A)
    exact iUnion_subset fun d => tensorChart_subset_span A d
  rw [heq]
  exact isSigma02_iUnion_tensorChart A

end NoUniversalFSigma.Proof.Packet
