module

public import NoUniversalFSigma.Branch
public import NoUniversalFSigma.Escape

@[expose] public section

/-! The branch family has diagonal escape rank at least one. -/

open Set Filter Topology

namespace NoUniversalFSigma.Proof.Branch

lemma exists_cylinder_subset_nhds (x : Point) {U : Set Point} (hU : U ∈ 𝓝 x) :
    ∃ n : ℕ, Cylinder (nodePrefix x n) ⊆ U := by
  rw [nhds_pi, Filter.mem_pi] at hU
  obtain ⟨J, hJ, t, ht, htU⟩ := hU
  obtain ⟨n, hn⟩ := hJ.bddAbove
  refine ⟨n + 1, fun y hy => htU fun i hi => ?_⟩
  have he : y i = x i :=
    (nodePrefix_eq_iff y (nodePrefix x (n + 1))).1 hy
      ⟨i, (hn hi).trans_lt (Nat.lt_succ_self n)⟩
  rw [he]
  exact mem_of_mem_nhds (ht i)

theorem diagonal_mem_escapeDerivative (x : Point) :
    (x, x) ∈ escapeDerivative j span.toAddSubgroup univ := by
  apply (mem_escapeDerivative_iff _ _ _ _).2
  refine ⟨mem_univ _, fun U hU hxU hbound => ?_⟩
  obtain ⟨V, hV, W, hW, hVW⟩ := mem_nhds_prod_iff.1 (hU.mem_nhds hxU)
  obtain ⟨n, hn⟩ := exists_cylinder_subset_nhds x (inter_mem hV hW)
  obtain ⟨z, hz, u, v, huv, hlim⟩ := escape_cylinder (nodePrefix x n)
  apply hz
  apply hbound
  apply mem_closure_of_tendsto hlim
  exact Eventually.of_forall fun m =>
    ⟨(u m, v m), ⟨mem_univ _, hVW ⟨(hn (huv m).1).1, (hn (huv m).2).2⟩⟩, rfl⟩

theorem diagonal_mem_escapeRemainder_one (x : Point) :
    (x, x) ∈ escapeRemainder j span.toAddSubgroup 1 := by
  rw [← show (0 : Ordinal) + 1 = 1 from zero_add 1]
  rw [escapeRemainder_add_one, escapeRemainder_zero]
  exact diagonal_mem_escapeDerivative x

end NoUniversalFSigma.Proof.Branch
