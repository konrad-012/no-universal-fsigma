module

public import NoUniversalFSigma.TensorCoordinates

@[expose] public section

/-! Splitting finite-support tensor coordinates at a finite packet. -/

namespace NoUniversalFSigma.Proof

open Set
open scoped lp

namespace PacketSplit

noncomputable section

variable {N : Type*} (I : N → Type*)

attribute [local instance] Classical.propDecidable

variable [DecidableEq N]

/-- A coordinate is a finite set of factors, with one coordinate chosen in each factor. -/
abbrev Coord := Σ F : Finset N, ∀ n : F, I n.val

/-- The equivalent finite-support choice presentation; zero denotes an unused factor. -/
abbrev Assignment := Π₀ n, WithZero (I n)

/-- A nonzero adjoined-zero coordinate records an ordinary coordinate. -/
def nonzeroEquiv (T : Type*) : {x : WithZero T // x ≠ 0} ≃ T where
  toFun x := WithZero.unzero x.property
  invFun t := ⟨t, WithZero.coe_ne_zero⟩
  left_inv := by intro x; apply Subtype.ext; exact WithZero.coe_unzero x.property
  right_inv := by intro t; rfl

/-- Recording the support identifies finitely supported choices with tensor coordinates. -/
noncomputable def assignmentEquiv : Assignment I ≃ Coord I := by
  exact DFinsupp.sigmaFinsetFunEquiv.trans
    (Equiv.sigmaCongrRight fun F => Equiv.piCongrRight fun n : F => nonzeroEquiv (I n.val))

@[simp]
theorem assignmentEquiv_fst (f : Assignment I) :
    (assignmentEquiv I f).1 = f.support := rfl

@[simp]
theorem assignmentEquiv_value (f : Assignment I) (n : f.support) :
    (((assignmentEquiv I f).2 n : I n.val) : WithZero (I n.val)) = f n.val := by
  exact WithZero.coe_unzero _

/-- A factor absent from the support contributes the scalar one. -/
def choiceValue (g : ∀ n, I n → ℝ) (n : N) : WithZero (I n) → ℝ :=
  WithZero.recZeroCoe 1 (g n)

omit [DecidableEq N] in
@[simp] theorem choiceValue_zero (g : ∀ n, I n → ℝ) (n : N) :
    choiceValue I g n 0 = 1 := rfl

omit [DecidableEq N] in
@[simp] theorem choiceValue_coe (g : ∀ n, I n → ℝ) (n : N) (i : I n) :
    choiceValue I g n i = g n i := rfl

/-- The scalar coordinate of an elementary product tensor. -/
noncomputable def coordProduct (g : ∀ n, I n → ℝ) (c : Coord I) : ℝ :=
  ∏ n : c.1, g n.val (c.2 n)

theorem coordProduct_assignmentEquiv (g : ∀ n, I n → ℝ) (f : Assignment I) :
    coordProduct I g (assignmentEquiv I f) = f.prod (choiceValue I g) := by
  rw [DFinsupp.prod, ← Finset.prod_coe_sort]
  apply Finset.prod_congr rfl
  intro n _
  change g n.val ((assignmentEquiv I f).2 n) = choiceValue I g n.val (f n.val)
  rw [← assignmentEquiv_value I f n]
  rfl

/-- Merge a finite packet and the finite-support choices on its complement. -/
noncomputable def merge (B : Finset N)
    (a : ∀ n : B, WithZero (I n.val))
    (g : Π₀ n : {n // n ∉ B}, WithZero (I n.val)) : Assignment I := by
  let T : Finset N := B ∪ g.support.image Subtype.val
  exact DFinsupp.mk T fun n => if h : n.val ∈ B then a ⟨n.val, h⟩ else g ⟨n.val, h⟩

@[simp]
theorem merge_apply_mem (B : Finset N) (a : ∀ n : B, WithZero (I n.val))
    (g : Π₀ n : {n // n ∉ B}, WithZero (I n.val)) {n : N} (hn : n ∈ B) :
    merge I B a g n = a ⟨n, hn⟩ := by
  simp only [merge, DFinsupp.mk_apply, Finset.mem_union, hn, true_or, dite_true]

@[simp]
theorem merge_apply_notMem (B : Finset N) (a : ∀ n : B, WithZero (I n.val))
    (g : Π₀ n : {n // n ∉ B}, WithZero (I n.val)) {n : N} (hn : n ∉ B) :
    merge I B a g n = g ⟨n, hn⟩ := by
  by_cases hg : (⟨n, hn⟩ : {n // n ∉ B}) ∈ g.support
  · have hnT : n ∈ B ∪ g.support.image Subtype.val :=
      Finset.mem_union_right _ (Finset.mem_image.mpr ⟨⟨n, hn⟩, hg, rfl⟩)
    simp only [merge, DFinsupp.mk_apply, hnT, dite_true, hn, dite_false]
  · have hnT : n ∉ B ∪ g.support.image Subtype.val := by
      simp only [Finset.mem_union, hn, false_or, Finset.mem_image]
      rintro ⟨m, hm, heq⟩
      have heq' : m = (⟨n, hn⟩ : {n // n ∉ B}) := Subtype.ext heq
      exact hg (heq' ▸ hm)
    rw [DFinsupp.notMem_support_iff.mp hg]
    simp only [merge, DFinsupp.mk_apply, hnT, dite_false]

/-- The full coordinate set factors into a finite packet and its outside coordinates. -/
noncomputable def assignmentSplit (B : Finset N) :
    Assignment I ≃ (∀ n : B, WithZero (I n.val)) ×
      (Π₀ n : {n // n ∉ B}, WithZero (I n.val)) where
  toFun f := (fun n => f n.val, f.subtypeDomain (fun n => n ∉ B))
  invFun p := merge I B p.1 p.2
  left_inv f := by
    ext n
    by_cases hn : n ∈ B
    · exact merge_apply_mem I B _ _ hn
    · rw [merge_apply_notMem I B _ _ hn]
      rfl
  right_inv p := by
    apply Prod.ext
    · funext n
      exact merge_apply_mem I B _ _ n.property
    · ext n
      exact merge_apply_notMem I B _ _ n.property

/-- The canonical tensor-factor coordinate equivalence at a finite cut. -/
noncomputable def coordSplit (B : Finset N) :
    Coord I ≃ (∀ n : B, Option (I n.val)) × Coord (fun n : {n // n ∉ B} => I n.val) :=
  (assignmentEquiv I).symm.trans ((assignmentSplit I B).trans
    (Equiv.prodCongr (Equiv.refl _) (assignmentEquiv _)))

theorem assignmentProduct_split (B : Finset N) (g : ∀ n, I n → ℝ)
    (f : Assignment I) :
    f.prod (choiceValue I g) =
      (∏ n : B, choiceValue I g n.val (f n.val)) *
        (f.subtypeDomain (fun n => n ∉ B)).prod
          (fun n x => choiceValue I g n.val x) := by
  let w : N → ℝ := fun n => choiceValue I g n (f n)
  have hfirst : (∏ n : B, w n.val) = ∏ n ∈ f.support ∩ B, w n := by
    rw [Finset.prod_coe_sort]
    symm
    apply Finset.prod_subset Finset.inter_subset_right
    intro n _ hn
    have hnf : n ∉ f.support := fun h => hn (Finset.mem_inter.mpr ⟨h, by assumption⟩)
    simp only [w, DFinsupp.notMem_support_iff.mp hnf, choiceValue_zero]
  have hsecond : (f.subtypeDomain (fun n => n ∉ B)).prod
      (fun n x => choiceValue I g n.val x) = ∏ n ∈ f.support \ B, w n := by
    have hs : (f.subtypeDomain (fun n => n ∉ B)).support =
        f.support.subtype (fun n => n ∉ B) := by
      ext n
      simp
    rw [DFinsupp.prod, hs]
    simp only [DFinsupp.subtypeDomain_apply]
    change (∏ i ∈ f.support.subtype (fun n => n ∉ B), w i.val) = _
    rw [Finset.prod_subtype_eq_prod_filter]
    congr 1
    ext n
    simp
  rw [hfirst, hsecond, Finset.prod_inter_mul_prod_sdiff]
  rfl

/-- Product coordinates factor exactly across a finite packet and its complement. -/
theorem coordProduct_split (B : Finset N) (g : ∀ n, I n → ℝ) (c : Coord I) :
    coordProduct I g c =
      (∏ n : B, choiceValue I g n.val ((coordSplit I B c).1 n)) *
        coordProduct (fun n : {n // n ∉ B} => I n.val)
          (fun n => g n.val) (coordSplit I B c).2 := by
  let f := (assignmentEquiv I).symm c
  have hc : assignmentEquiv I f = c := (assignmentEquiv I).apply_symm_apply c
  have hsplit : coordSplit I B (assignmentEquiv I f) =
      (fun n : B => f n.val,
        assignmentEquiv _ (f.subtypeDomain (fun n => n ∉ B))) := by
    simp only [coordSplit, Equiv.trans_apply, Equiv.symm_apply_apply,
      assignmentSplit, Equiv.coe_fn_mk]
    rfl
  rw [← hc, coordProduct_assignmentEquiv, hsplit, coordProduct_assignmentEquiv]
  exact assignmentProduct_split I B g f

/-- The resulting factorization is a linear isometry for the norm Hilbert topology. -/
noncomputable def hilbertSplit (B : Finset N) :
    ℓ²(Coord I, ℝ) ≃ₗᵢ[ℝ]
      ℓ²((∀ n : B, Option (I n.val)) × Coord (fun n : {n // n ∉ B} => I n.val), ℝ) :=
  hilbertReindex (coordSplit I B)

end

end PacketSplit

end NoUniversalFSigma.Proof
