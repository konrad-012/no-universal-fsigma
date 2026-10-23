module

public import NoUniversalFSigma.TensorCoordinates

@[expose] public section

/-! Square-summable finite tensor coordinates indexed by dependent finite products. -/

namespace NoUniversalFSigma.Proof

open Set
open scoped lp

private def FiniteProductSummable (S : Type) [Fintype S] : Prop :=
  ∀ (D : S → Type) (f : ∀ s, D s → ℝ),
    (∀ s i, 0 ≤ f s i) → (∀ s, Summable (f s)) →
    Summable (fun x : ∀ s, D s => ∏ s, f s (x s)) ∧
      (∑' x : ∀ s, D s, ∏ s, f s (x s)) = ∏ s, ∑' i, f s i

private theorem finiteProductSummable (S : Type) [Fintype S] : FiniteProductSummable S := by
  classical
  refine Fintype.induction_empty_option (P := FiniteProductSummable) ?_ ?_ ?_ S
  · intro A B _ e ih
    let : Fintype A := Fintype.ofEquiv B e.symm
    intro D f hn hs
    let g : ∀ a : A, D (e a) → ℝ := fun a => f (e a)
    obtain ⟨hgs, hge⟩ := ih (fun a => D (e a)) g (fun a => hn (e a)) (fun a => hs (e a))
    let E : (∀ b : B, D b) ≃ (∀ a : A, D (e a)) := Equiv.piCongrLeft' D e.symm
    have hcomp : (fun x : ∀ b : B, D b => ∏ b, f b (x b)) =
        (fun x : ∀ a : A, D (e a) => ∏ a, g a (x a)) ∘ E := by
      funext x
      exact (e.prod_comp (fun b => f b (x b))).symm
    rw [hcomp]
    refine ⟨E.summable_iff.mpr hgs, ?_⟩
    change (∑' x, (∏ a, g a ((E x) a))) = _
    rw [E.tsum_eq (fun x => ∏ a, g a (x a)), hge]
    exact e.prod_comp (fun b => ∑' i, f b i)
  · intro D f _hn _hs
    let : Unique (∀ s : PEmpty, D s) :=
      ⟨⟨fun s => PEmpty.elim s⟩, fun x => funext fun s => PEmpty.elim s⟩
    exact ⟨(hasSum_fintype _).summable, by simp⟩
  · intro A _ ih D f hn hs
    obtain ⟨hts, hte⟩ := ih (fun a => D (some a)) (fun a => f (some a))
      (fun a => hn (some a)) (fun a => hs (some a))
    have hp := (hs none).mul_of_nonneg hts (hn none)
      (fun x => Finset.prod_nonneg fun a _ => hn (some a) (x a))
    let E : (∀ s : Option A, D s) ≃ D none × (∀ a : A, D (some a)) :=
      Equiv.piOptionEquivProd
    have hcomp : (fun x : ∀ s : Option A, D s => ∏ s, f s (x s)) =
        (fun x : D none × (∀ a : A, D (some a)) =>
          f none x.1 * ∏ a, f (some a) (x.2 a)) ∘ E := by
      funext x
      exact Fintype.prod_option _
    rw [hcomp]
    refine ⟨E.summable_iff.mpr hp, ?_⟩
    change (∑' x, f none (E x).1 * ∏ a, f (some a) ((E x).2 a)) = _
    rw [E.tsum_eq (fun x => f none x.1 * ∏ a, f (some a) (x.2 a)),
      ← (hs none).tsum_mul_tsum hts hp, hte]
    exact (Fintype.prod_option (fun s : Option A => ∑' i, f s i)).symm

/-- Tonelli's finite-product identity for nonnegative summable real families. -/
theorem summable_pi_prod (S : Type) [Fintype S] (D : S → Type)
    (f : ∀ s, D s → ℝ) (hnonneg : ∀ s i, 0 ≤ f s i) (hsum : ∀ s, Summable (f s)) :
    Summable (fun x : ∀ s, D s => ∏ s, f s (x s)) ∧
      (∑' x : ∀ s, D s, ∏ s, f s (x s)) = ∏ s, ∑' i, f s i :=
  finiteProductSummable S D f hnonneg hsum

/-- A finite product of square-summable coordinate vectors is square summable. -/
theorem memℓp_hilbertPi (S : Type) [Fintype S] (D : S → Type)
    (x : ∀ s, ℓ²(D s, ℝ)) : Memℓp (fun c : ∀ s, D s => ∏ s, x s (c s)) 2 := by
  apply memℓp_gen
  have h := (summable_pi_prod S D (fun s i => ‖x s i‖ ^ 2)
    (fun _ _ => sq_nonneg _) (fun s => hilbert_summable_sq (x s))).1
  simpa only [ENNReal.toReal_ofNat, Real.rpow_two, norm_prod, ← Finset.prod_pow] using h

/-- The elementary tensor over a dependent finite family of coordinate Hilbert spaces. -/
noncomputable def hilbertPi (S : Type) [Fintype S] (D : S → Type)
    (x : ∀ s, ℓ²(D s, ℝ)) : ℓ²((∀ s, D s), ℝ) :=
  ⟨fun c => ∏ s, x s (c s), memℓp_hilbertPi S D x⟩

@[simp]
theorem hilbertPi_apply (S : Type) [Fintype S] (D : S → Type)
    (x : ∀ s, ℓ²(D s, ℝ)) (c : ∀ s, D s) : hilbertPi S D x c = ∏ s, x s (c s) := rfl

theorem norm_hilbertPi (S : Type) [Fintype S] (D : S → Type)
    (x : ∀ s, ℓ²(D s, ℝ)) : ‖hilbertPi S D x‖ = ∏ s, ‖x s‖ := by
  have h := (summable_pi_prod S D (fun s i => ‖x s i‖ ^ 2)
    (fun _ _ => sq_nonneg _) (fun s => hilbert_summable_sq (x s))).2
  have heq : ‖hilbertPi S D x‖ ^ 2 = (∏ s, ‖x s‖) ^ 2 := by
    calc
      ‖hilbertPi S D x‖ ^ 2 = ∑' c : ∀ s, D s, ∏ s, ‖x s (c s)‖ ^ 2 := by
        rw [hilbert_norm_sq]
        apply tsum_congr
        intro c
        simp only [hilbertPi_apply, norm_prod, ← Finset.prod_pow]
      _ = ∏ s, ∑' i, ‖x s i‖ ^ 2 := h
      _ = ∏ s, ‖x s‖ ^ 2 := by
        exact Finset.prod_congr rfl fun s _ => (hilbert_norm_sq (x s)).symm
      _ = (∏ s, ‖x s‖) ^ 2 := Finset.prod_pow _ _ _
  have hprod : 0 ≤ ∏ s, ‖x s‖ := by positivity
  nlinarith [norm_nonneg (hilbertPi S D x)]

/-- Finite elementary tensors depend multilinearly on their factors. -/
noncomputable def hilbertPiMultilinear (S : Type) [Fintype S] (D : S → Type) :
    MultilinearMap ℝ (fun s => ℓ²(D s, ℝ)) ℓ²((∀ s, D s), ℝ) where
  toFun := hilbertPi S D
  map_update_add' m i x y := by
    ext c
    change (∏ s, (Function.update m i (x + y)) s (c s)) =
      (∏ s, (Function.update m i x) s (c s)) +
        ∏ s, (Function.update m i y) s (c s)
    simp_rw [Function.apply_update (fun s (v : ℓ²(D s, ℝ)) => v (c s))]
    simp [Finset.prod_update_of_mem, add_mul]
  map_update_smul' m i a x := by
    ext c
    change (∏ s, (Function.update m i (a • x)) s (c s)) =
      a * ∏ s, (Function.update m i x) s (c s)
    simp_rw [Function.apply_update (fun s (v : ℓ²(D s, ℝ)) => v (c s))]
    simp [Finset.prod_update_of_mem, mul_assoc]

/-- The norm-one continuous multilinear elementary tensor map. -/
noncomputable def hilbertPiContinuousMultilinear (S : Type) [Fintype S] (D : S → Type) :
    ContinuousMultilinearMap ℝ (fun s => ℓ²(D s, ℝ)) ℓ²((∀ s, D s), ℝ) :=
  (hilbertPiMultilinear S D).mkContinuous 1 fun x => by
    change ‖hilbertPi S D x‖ ≤ 1 * ∏ s, ‖x s‖
    rw [norm_hilbertPi, one_mul]

theorem continuous_hilbertPi (S : Type) [Fintype S] (D : S → Type) :
    Continuous (hilbertPi S D) :=
  (hilbertPiContinuousMultilinear S D).cont

end NoUniversalFSigma.Proof
