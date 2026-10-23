module

public import NoUniversalFSigma.Definitions

/-! The three elementary `Fσ` closure properties needed by the proof. -/

@[expose] public section

namespace NoUniversalFSigma.BorelHierarchy

open Set

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] {s t : Set X}

theorem isPi01_isSigma02 (h : IsPi01 s) : IsSigma02 s :=
  ⟨fun _ => s, fun _ => h, (iUnion_const s).symm⟩

theorem isSigma02_inter (hs : IsSigma02 s) (ht : IsSigma02 t) : IsSigma02 (s ∩ t) := by
  obtain ⟨f, hf, rfl⟩ := hs
  obtain ⟨g, hg, rfl⟩ := ht
  refine ⟨fun n => f n.unpair.1 ∩ g n.unpair.2, fun n => (hf _).inter (hg _), ?_⟩
  ext x
  simp only [Set.mem_inter_iff, Set.mem_iUnion]
  constructor
  · rintro ⟨⟨n, hn⟩, ⟨m, hm⟩⟩
    exact ⟨Nat.pair n m, by simpa using And.intro hn hm⟩
  · rintro ⟨n, hn, hm⟩
    exact ⟨⟨_, hn⟩, ⟨_, hm⟩⟩

theorem isSigma02_preimage {f : X → Y} (hf : Continuous f) {s : Set Y}
    (h : IsSigma02 s) : IsSigma02 (f ⁻¹' s) := by
  obtain ⟨g, hg, rfl⟩ := h
  exact ⟨fun n => f ⁻¹' g n, fun n => (hg n).preimage hf, by rw [preimage_iUnion]⟩

end NoUniversalFSigma.BorelHierarchy
