module

public import NoUniversalFSigma.PacketRecovery

@[expose] public section

/-! Closedness of the countable tensor charts by continuous recovery. -/

noncomputable section

namespace NoUniversalFSigma.Proof.Packet

open Set Topology NoUniversalFSigma
open scoped lp

variable (A : ℕ → AdmissibleFamily)

/-- The two disjoint pinning packets recover every product-label coordinate, including
coordinates used by one of the packets themselves. -/
theorem isClosed_tensorChart (d : TensorChartIndex A) : IsClosed (tensorChart A d) := by
  apply isClosed_mixtureChart (mix A d.B) (continuous_mix A d.B)
    (coefficientSet A d) (isClosed_coefficientSet A d) (pinSet A d) (isClosed_pinSet A d)
    (fun n : {n // n ∉ d.B} => (A n.val).j)
    (fun n => (A n.val).closedEmbedding)
    (fun c => chartCoeff A d c) (fun c => (chartCoeff A d c).continuous)
    (fun c v => v (d.coord c))
    (fun c => (lp.evalCLM ℝ (fun _ : HeadCoord A d.B => ℝ) 2 (d.coord c)).continuous)
    (fun c v hv => coefficientSet_nonzero A d c hv)
    (fun c n => chartRecover A d c n) (fun c n => (chartRecover A d c n).continuous)
  · intro v q hq c
    exact chartCoeff_sum A d v q hq c
  · intro v q hq c n
    exact chartRecover_sum A d v q hq c n

/-- Only countably many closed charts occur. -/
theorem isSigma02_iUnion_tensorChart :
    IsSigma02 (⋃ d : TensorChartIndex A, tensorChart A d) := by
  obtain ⟨e, he⟩ := exists_surjective_nat (TensorChartIndex A)
  refine ⟨fun n => tensorChart A (e n), fun n => isClosed_tensorChart A (e n), ?_⟩
  exact (Function.Surjective.iUnion_comp he _).symm

end NoUniversalFSigma.Proof.Packet
