module

public import NoUniversalFSigma.BranchFamily
public import NoUniversalFSigma.BranchEscape
public import NoUniversalFSigma.Successor
public import NoUniversalFSigma.PacketInsertion
public import NoUniversalFSigma.Comparison

@[expose] public section

/-! Transfinite construction of admissible families of arbitrary countable diagonal rank. -/

noncomputable section

namespace NoUniversalFSigma.Proof

open Set Filter Topology NoUniversalFSigma
open scoped lp Ordinal

namespace Packet

/-- Package the countable tensor family once its algebraic span is known to be `Fσ`. -/
def familyOfSigma02 (A : ℕ → AdmissibleFamily)
    (hspan : IsSigma02 (span A : Set (Space A))) : AdmissibleFamily where
  Coord := Coord A
  Param := Param A
  j := j A
  closedEmbedding := isClosedEmbedding_j A
  bound := ∑' F, majorant F
  bound_nonneg := tsum_nonneg majorant_nonneg
  norm_le := norm_j_le A
  mass := mass A
  mass_one := mass_one A
  features := features A
  features_locallyConstant := features_locallyConstant A
  features_separate := features_separate A
  span_isSigma02 := hspan

end Packet

/-- The branch family supplies rank one for the successor operation. -/
theorem branch_family_diagonal_rank_one : ∀ p,
    (p, p) ∈ escapeRemainder Branch.family.j Branch.family.span.toAddSubgroup 1 :=
  Branch.diagonal_mem_escapeRemainder_one

/-- The transfinite recursion, with the countable tensor span lemma exposed as its sole
construction input. The successor and limit rank proofs are for the concrete constructions. -/
theorem exists_rankFamily_of_packet_span
    (hpacket : ∀ A : ℕ → AdmissibleFamily, IsSigma02 (Packet.span A : Set (Packet.Space A))) :
    ∀ α : Ordinal, α < ω₁ → ∃ A : AdmissibleFamily,
      ∀ p, (p, p) ∈ escapeRemainder A.j A.span.toAddSubgroup α := by
  intro α
  induction α using Ordinal.limitRecOn with
  | zero =>
    intro _hα
    exact ⟨Branch.family, fun _ => by simp⟩
  | add_one α ih =>
    intro hα
    obtain ⟨A, hA⟩ := ih ((lt_add_one α).trans hα)
    exact ⟨A.successor Branch.family,
      A.successor_diagonal_rank Branch.family α hA branch_family_diagonal_rank_one⟩
  | limit lambda hlambda ih =>
    intro hcount
    let : Countable (Iio lambda) :=
      (Cardinal.countable_Iio_of_lt_omega_one hcount).to_subtype
    let : Nonempty (Iio lambda) := ⟨⟨0, hlambda.bot_lt⟩⟩
    obtain ⟨e, he⟩ := exists_surjective_nat (Iio lambda)
    have hex : ∀ β : Iio lambda, ∃ A : AdmissibleFamily,
        ∀ p, (p, p) ∈ escapeRemainder A.j A.span.toAddSubgroup β.1 :=
      fun β => ih β.1 β.2 (β.2.trans hcount)
    choose A hA using hex
    let B : ℕ → AdmissibleFamily := fun n => A (e n)
    refine ⟨Packet.familyOfSigma02 B (hpacket B), ?_⟩
    apply Packet.cofinal_rank B (fun n => (e n).1) lambda hlambda
    · intro β hβ
      obtain ⟨n, hn⟩ := he ⟨β, hβ⟩
      exact ⟨n, by rw [hn]⟩
    · intro n
      exact hA (e n)

/-- Applying the countable-rank construction to a target's termination bound produces
an admissible coset relation that does not Baire-reduce to that target. -/
theorem exists_admissible_not_baireReducible_of_packet_span
    (hpacket : ∀ A : ℕ → AdmissibleFamily, IsSigma02 (Packet.span A : Set (Packet.Space A)))
    {Y : Type} [TopologicalSpace Y] [PolishSpace Y] (F : NoUniversalFSigma.EquivRel Y)
    (hF : IsSigma02 F.toGraph) : ∃ A : AdmissibleFamily,
      ¬ BaireReducible (cosetRel A.span.toAddSubgroup) F := by
  obtain ⟨K, α, hα, hempty⟩ := exists_exhaustion_countable_bound F hF
  obtain ⟨A, hA⟩ := exists_rankFamily_of_packet_span hpacket α hα
  exact ⟨A, not_baireReducible_of_diagonal_rank K A.span.toAddSubgroup A.j A.continuous_j
    (fun t => A.span.mem_toAddSubgroup.mpr (A.j_mem_span t)) α hA hempty⟩

/-- Final nonuniversality assembly, with the countable tensor span lemma as its explicit input. -/
theorem not_isUniversalFSigma_of_packet_span
    (hpacket : ∀ A : ℕ → AdmissibleFamily, IsSigma02 (Packet.span A : Set (Packet.Space A)))
    {Y : Type} [TopologicalSpace Y] [PolishSpace Y] [MeasurableSpace Y] [BorelSpace Y]
    (E : NoUniversalFSigma.EquivRel Y) (hE : IsSigma02 E.toGraph) :
    ∃ (X : Type) (_ : TopologicalSpace X) (_ : PolishSpace X) (_ : MeasurableSpace X)
      (_ : BorelSpace X) (F : NoUniversalFSigma.EquivRel X),
      IsSigma02 F.toGraph ∧ ¬ NoUniversalFSigma.BorelReducible F E := by
  obtain ⟨A, hA⟩ := exists_admissible_not_baireReducible_of_packet_span hpacket E hE
  refine ⟨A.Space, inferInstance, inferInstance, inferInstance, inferInstance,
    cosetRel A.span.toAddSubgroup,
    isSigma02_cosetRel A.span.toAddSubgroup A.isSigma02_span, ?_⟩
  exact fun h => hA (baireReducible_of_borelReducible h)

end NoUniversalFSigma.Proof
