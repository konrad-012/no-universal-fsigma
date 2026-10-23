module

public import NoUniversalFSigma.CountableTensor
public import NoUniversalFSigma.RankFamilies

@[expose] public section

/-! No `Fσ` equivalence relation is universal for Borel reducibility. -/

namespace NoUniversalFSigma.Proof

open Set NoUniversalFSigma

/-- There is no universal `Fσ` equivalence relation under Borel reducibility. -/
theorem not_isUniversalFSigma
    {Y : Type} [TopologicalSpace Y] [PolishSpace Y] [MeasurableSpace Y] [BorelSpace Y]
    (E : EquivRel Y) (hE : IsSigma02 E.toGraph) :
    ∃ (X : Type) (_ : TopologicalSpace X) (_ : PolishSpace X) (_ : MeasurableSpace X)
      (_ : BorelSpace X) (F : EquivRel X), IsSigma02 F.toGraph ∧ ¬ BorelReducible F E :=
  not_isUniversalFSigma_of_packet_span Packet.isSigma02_span E hE

end NoUniversalFSigma.Proof
