module

public import NoUniversalFSigma.Main

@[expose] public section

namespace NoUniversalFSigma

/-- Every `Fσ` equivalence relation fails to receive a Borel reduction from some
`Fσ` equivalence relation on a Polish space. -/
theorem not_isUniversalFSigma
    {Y : Type} [TopologicalSpace Y] [PolishSpace Y] [MeasurableSpace Y] [BorelSpace Y]
    (E : EquivRel Y) (hE : IsSigma02 E.toGraph) :
    ∃ (X : Type) (_ : TopologicalSpace X) (_ : PolishSpace X)
      (_ : MeasurableSpace X) (_ : BorelSpace X) (F : EquivRel X),
      IsSigma02 F.toGraph ∧ ¬ BorelReducible F E :=
  Proof.not_isUniversalFSigma E hE

end NoUniversalFSigma
