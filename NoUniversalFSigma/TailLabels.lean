module

public import Mathlib

@[expose] public section

/-! Finite witness selection for countable tensor charts. -/

namespace NoUniversalFSigma.Proof

open Set

/-- Two product labels agree except at finitely many coordinates. -/
def FiniteDifference {Q : ℕ → Type*} (q r : ∀ n, Q n) : Prop :=
  {n | q n ≠ r n}.Finite

theorem finiteDifference_refl {Q : ℕ → Type*} (q : ∀ n, Q n) :
    FiniteDifference q q := by simp [FiniteDifference]

theorem finiteDifference_symm {Q : ℕ → Type*} {q r : ∀ n, Q n}
    (h : FiniteDifference q r) : FiniteDifference r q := by
  simpa only [FiniteDifference, ne_comm] using h

theorem finiteDifference_trans {Q : ℕ → Type*} {q r s : ∀ n, Q n}
    (hqr : FiniteDifference q r) (hrs : FiniteDifference r s) : FiniteDifference q s := by
  apply (hqr.union hrs).subset
  intro n hn
  by_cases h : q n = r n
  · exact Or.inr (fun h' => hn (h.trans h'))
  · exact Or.inl h

/-- A single finite cut handles all finitely differing pairs among finitely many labels. -/
theorem exists_common_tail_cut {S : Type*} [Finite S] {Q : ℕ → Type*}
    (q : S → ∀ n, Q n) :
    ∃ B : Finset ℕ, ∀ c d, FiniteDifference (q c) (q d) →
      ∀ n, n ∉ B → q c n = q d n := by
  classical
  let _ : Fintype S := Fintype.ofFinite S
  let D (c d : S) : Finset ℕ :=
    if h : FiniteDifference (q c) (q d) then h.toFinset else ∅
  let B : Finset ℕ := Finset.univ.biUnion fun c => Finset.univ.biUnion fun d => D c d
  refine ⟨B, ?_⟩
  intro c d hcd n hn
  by_contra hne
  apply hn
  apply Finset.mem_biUnion.mpr
  refine ⟨c, Finset.mem_univ _, Finset.mem_biUnion.mpr ?_⟩
  refine ⟨d, Finset.mem_univ _, ?_⟩
  dsimp only [D]
  rw [dite_eq_left hcd]
  exact hcd.mem_toFinset.mpr hne

/-- Infinitely differing labels retain an infinite choice of witnesses after every finite cut. -/
theorem infinite_tail_differences {Q : ℕ → Type*} {q r : ∀ n, Q n}
    (h : ¬ FiniteDifference q r) (B : Finset ℕ) :
    {n | n ∉ B ∧ q n ≠ r n}.Infinite := by
  convert (show {n | q n ≠ r n}.Infinite from h).sdiff B.finite_toSet using 1
  ext n
  exact and_comm

/-- Finitely many infinite sets admit pairwise distinct representatives. -/
theorem exists_injective_finite_choice {S : Type*} [Finite S]
    (D : S → Set ℕ) (hD : ∀ s, (D s).Infinite) :
    ∃ f : S → ℕ, Function.Injective f ∧ ∀ s, f s ∈ D s := by
  classical
  let _ : Fintype S := Fintype.ofFinite S
  have haux (T : Finset S) : ∃ f : S → ℕ,
      Set.InjOn f (T : Set S) ∧ ∀ s ∈ T, f s ∈ D s := by
    induction T using Finset.induction_on with
    | empty => exact ⟨fun _ => 0, by simp, by simp⟩
    | @insert s T hs ih =>
      obtain ⟨f, hf, hfD⟩ := ih
      obtain ⟨n, hnD, hnrange⟩ := ((hD s).sdiff
        (T.finite_toSet.image f)).nonempty
      refine ⟨Function.update f s n, ?_, ?_⟩
      · intro a ha b hb hab
        simp only [Finset.coe_insert, Set.mem_insert_iff, Finset.mem_coe] at ha hb
        rcases ha with has | ha
        · subst a
          rcases hb with hbs | hb
          · exact hbs.symm
          · have hbs : b ≠ s := fun h => hs (h ▸ hb)
            rw [Function.update_self, Function.update_of_ne hbs] at hab
            exact False.elim (hnrange ⟨b, hb, hab.symm⟩)
        · rcases hb with hbs | hb
          · subst b
            have has : a ≠ s := fun h => hs (h ▸ ha)
            rw [Function.update_of_ne has, Function.update_self] at hab
            exact False.elim (hnrange ⟨a, ha, hab⟩)
          · have has : a ≠ s := fun h => hs (h ▸ ha)
            have hbs : b ≠ s := fun h => hs (h ▸ hb)
            rw [Function.update_of_ne has, Function.update_of_ne hbs] at hab
            exact hf ha hb hab
      · intro a ha
        rcases Finset.mem_insert.mp ha with rfl | ha
        · simpa using hnD
        · have has : a ≠ s := fun h => hs (h ▸ ha)
          simpa only [Function.update_of_ne has] using hfD a ha
  obtain ⟨f, hf, hfD⟩ := haux Finset.univ
  exact ⟨f, fun _ _ h => hf (by simp) (by simp) h, fun s => hfD s (by simp)⟩

/-- Two disjoint finite witness sets can distinguish all ordered pairs of distinct tails. -/
theorem exists_disjoint_tail_witnesses {S : Type*} [Finite S] {Q : ℕ → Type*}
    (q : S → ∀ n, Q n)
    (h : ∀ c d, c ≠ d → ¬ FiniteDifference (q c) (q d)) (B : Finset ℕ) :
    ∃ f : ({p : S × S // p.1 ≠ p.2} × Fin 2) → ℕ,
      Function.Injective f ∧ ∀ p,
        f p ∉ B ∧ q p.1.val.1 (f p) ≠ q p.1.val.2 (f p) := by
  classical
  exact exists_injective_finite_choice
    (fun p : {p : S × S // p.1 ≠ p.2} × Fin 2 =>
      {n | n ∉ B ∧ q p.1.val.1 n ≠ q p.1.val.2 n})
    (fun p => infinite_tail_differences (h _ _ p.1.property) B)

end NoUniversalFSigma.Proof
