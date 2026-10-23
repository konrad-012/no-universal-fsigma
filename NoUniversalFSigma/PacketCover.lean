module

public import NoUniversalFSigma.PacketChartData
public import NoUniversalFSigma.TailLabels

@[expose] public section

/-! Regrouping finite packet sums and selecting finite normalized pinning features. -/

noncomputable section

namespace NoUniversalFSigma.Proof.Packet

open Set Topology NoUniversalFSigma
open scoped lp

attribute [local instance] Classical.propDecidable

variable (A : ℕ → AdmissibleFamily)

/-- Mixing with a fixed tail is linear in the finite-head coefficient. -/
def mixLinear (B : Finset ℕ) (q : TailParam A B) : HeadSpace A B →ₗ[ℝ] Space A where
  toFun v := mix A B v q
  map_add' := fun v w => mix_add A B v w q
  map_smul' := fun c v => mix_smul A B c v q

@[simp]
theorem mix_zero (B : Finset ℕ) (q : TailParam A B) : mix A B 0 q = 0 :=
  (mixLinear A B q).map_zero

theorem mix_sum {S : Type*} (B : Finset ℕ) (q : TailParam A B)
    (T : Finset S) (v : S → HeadSpace A B) :
    mix A B (∑ s ∈ T, v s) q = ∑ s ∈ T, mix A B (v s) q :=
  map_sum (mixLinear A B q) v T

private def labelSetoid {S : Type*} (q : S → Param A) : Setoid S where
  r c d := FiniteDifference (q c) (q d)
  iseqv := ⟨fun _ => finiteDifference_refl _, fun h => finiteDifference_symm h,
    fun h h' => finiteDifference_trans h h'⟩

/-- A finite packet sum can be grouped by eventual agreement of its parameter labels.
Zero vector coefficients are discarded, leaving pairwise infinitely differing labels. -/
theorem regroup_finite_sum (r : ℕ) (a : Fin r → ℝ) (q : Fin r → Param A) :
    ∃ (B : Finset ℕ) (m : ℕ) (v : Fin m → HeadSpace A B) (p : Fin m → Param A),
      (∀ c, v c ∈ Submodule.span ℝ (range (finitePacket A B))) ∧
      (∀ c, v c ≠ 0) ∧
      (∀ c d, c ≠ d → ¬ FiniteDifference (p c) (p d)) ∧
      ∑ i, a i • j A (q i) = ∑ c, mix A B (v c) (restrictParam A B (p c)) := by
  classical
  obtain ⟨B, hB⟩ := exists_common_tail_cut q
  let R := labelSetoid A q
  let C := Quotient R
  let rep (c : C) : Fin r := c.out
  let tail (c : C) := restrictParam A B (q (rep c))
  let v (c : C) : HeadSpace A B :=
    ∑ i ∈ Finset.univ.filter (fun i : Fin r => Quotient.mk R i = c),
      a i • finitePacket A B (restrictHead A B (q i))
  have htail (c : C) (i : Fin r) (hi : Quotient.mk R i = c) :
      restrictParam A B (q i) = tail c := by
    have hrel : FiniteDifference (q i) (q (rep c)) :=
      Quotient.exact (hi.trans (Quotient.out_eq c).symm)
    funext n
    exact hB i (rep c) hrel n.val n.property
  have hv (c : C) : v c ∈ Submodule.span ℝ (range (finitePacket A B)) := by
    apply Submodule.sum_mem
    intro i _
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, rfl⟩)
  have hgroup : ∑ c : C, mix A B (v c) (tail c) = ∑ i, a i • j A (q i) := by
    calc
      ∑ c : C, mix A B (v c) (tail c) =
          ∑ c : C, ∑ i ∈ Finset.univ.filter (fun i : Fin r => Quotient.mk R i = c),
            a i • j A (q i) := by
        apply Finset.sum_congr rfl
        intro c _
        dsimp only [v]
        rw [mix_sum]
        apply Finset.sum_congr rfl
        intro i hi
        rw [mix_smul, j_eq_mix A B (q i), htail c i (Finset.mem_filter.mp hi).2]
      _ = ∑ i, a i • j A (q i) := Finset.sum_fiberwise _ (Quotient.mk R) _
  let Active := {c : C // v c ≠ 0}
  have hactive : ∑ c : Active, mix A B (v c.val) (tail c.val) =
      ∑ c : C, mix A B (v c) (tail c) := by
    have h := Fintype.sum_subtype_add_sum_subtype (fun c : C => v c ≠ 0)
      (fun c => mix A B (v c) (tail c))
    have hzero : (∑ c : {c : C // ¬ v c ≠ 0}, mix A B (v c.val) (tail c.val)) = 0 := by
      apply Finset.sum_eq_zero
      intro c _
      rw [not_not.mp c.property, mix_zero]
    rw [hzero, add_zero] at h
    exact h
  let m := Fintype.card Active
  let e : Fin m ≃ Active := (Fintype.equivFin Active).symm
  refine ⟨B, m, fun c => v (e c).val, fun c => q (rep (e c).val),
    fun c => hv _, fun c => (e c).property, ?_, ?_⟩
  · intro c d hcd hfd
    have hclass : (e c).val = (e d).val := by
      have he := Quotient.sound (s := R) hfd
      simpa only [rep, Quotient.out_eq] using he
    exact hcd (e.injective (Subtype.ext hclass))
  · rw [← hgroup, ← hactive]
    exact (Fintype.sum_equiv e _ _ (fun _ => rfl)).symm

/-- Every vector in the algebraic packet span has a reduced finite mixture representation. -/
theorem exists_reduced_mixture {z : Space A} (hz : z ∈ span A) :
    ∃ (B : Finset ℕ) (m : ℕ) (v : Fin m → HeadSpace A B) (p : Fin m → Param A),
      (∀ c, v c ∈ Submodule.span ℝ (range (finitePacket A B))) ∧
      (∀ c, v c ≠ 0) ∧
      (∀ c d, c ≠ d → ¬ FiniteDifference (p c) (p d)) ∧
      z = ∑ c, mix A B (v c) (restrictParam A B (p c)) := by
  obtain ⟨r, a, g, hg⟩ := Submodule.mem_span_set'.mp hz
  choose q hq using fun i : Fin r => (g i).property
  obtain ⟨B, m, v, p, hv, hne, hsep, hsum⟩ := regroup_finite_sum A r a q
  refine ⟨B, m, v, p, hv, hne, hsep, ?_⟩
  rw [← hsum, ← hg]
  exact Finset.sum_congr rfl fun i _ => congrArg (a i • ·) (hq i).symm

private abbrev OrderedPair (m : ℕ) := {p : Fin m × Fin m // p.1 ≠ p.2}

private theorem exists_deltaFeature (B : Finset ℕ) (m : ℕ)
    (p : Fin m → TailParam A B) (W : Finset {n // n ∉ B})
    (code : W → OrderedPair m) (loc : OrderedPair m → W)
    (hcode : ∀ t, code (loc t) = t)
    (hsep : ∀ w : W, p (code w).val.1 w.val ≠ p (code w).val.2 w.val) :
    ∃ a : Fin m → WitnessFeature A B W, ∀ c d,
      witnessValue A B W (a c) (p d) = if c = d then 1 else 0 := by
  have hn (c : Fin m) (w : W) (hc : (code w).val.1 = c) :=
    (A w.val.val).exists_normalizedFeature
      (show p c w.val ≠ p (code w).val.2 w.val by rw [← hc]; exact hsep w)
  let a : Fin m → WitnessFeature A B W := fun c w =>
    if h : (code w).val.1 = c then (hn c w h).choose else .inl ()
  have hapos (c : Fin m) (w : W) (hc : (code w).val.1 = c) :
      a c w = (hn c w hc).choose := by
    exact dite_eq_left hc
  have haneg (c : Fin m) (w : W) (hc : (code w).val.1 ≠ c) :
      a c w = (.inl () : (A w.val.val).NormalizedFeature) := by
    exact dite_eq_right hc
  have hone (c : Fin m) (w : W) :
      hilbertFinsuppFunctional ((A w.val.val).normalizedFunctional (a c w))
        ((A w.val.val).j (p c w.val)) = 1 := by
    by_cases hc : (code w).val.1 = c
    · rw [hapos c w hc]
      exact (hn c w hc).choose_spec.1
    · rw [haneg c w hc]
      exact (A w.val.val).mass_one (p c w.val)
  refine ⟨a, ?_⟩
  intro c d
  by_cases hcd : c = d
  · subst d
    simp only [witnessValue, hone, Finset.prod_const_one, ↓reduceIte]
  · rw [ite_eq_right hcd]
    let t : OrderedPair m := ⟨(c, d), hcd⟩
    let w : W := loc t
    have hcw : (code w).val.1 = c := congrArg (fun t => t.val.1) (hcode t)
    have hdw : (code w).val.2 = d := congrArg (fun t => t.val.2) (hcode t)
    have hzero : hilbertFinsuppFunctional ((A w.val.val).normalizedFunctional (a c w))
        ((A w.val.val).j (p d w.val)) = 0 := by
      rw [hapos c w hcw]
      exact hdw ▸ (hn c w hcw).choose_spec.2
    exact Finset.prod_eq_zero (Finset.mem_univ w) hzero

/-- Infinitely differing labels admit two disjoint finite packets of normalized delta features. -/
theorem exists_disjoint_delta_features (B : Finset ℕ) (m : ℕ) (p : Fin m → Param A)
    (hp : ∀ c d, c ≠ d → ¬ FiniteDifference (p c) (p d)) :
    ∃ (W1 W2 : Finset {n // n ∉ B}), Disjoint W1 W2 ∧
      ∃ (a1 : Fin m → WitnessFeature A B W1) (a2 : Fin m → WitnessFeature A B W2),
        ∀ c d,
          witnessValue A B W1 (a1 c) (restrictParam A B (p d)) =
            (if c = d then 1 else 0) ∧
          witnessValue A B W2 (a2 c) (restrictParam A B (p d)) =
            (if c = d then 1 else 0) := by
  classical
  obtain ⟨f, hf, hfp⟩ := exists_disjoint_tail_witnesses p hp B
  let w (t : OrderedPair m × Fin 2) : {n // n ∉ B} := ⟨f t, (hfp t).1⟩
  have hw : Function.Injective w := fun t u h => hf (congrArg Subtype.val h)
  let W (r : Fin 2) : Finset {n // n ∉ B} := Finset.univ.image fun t : OrderedPair m => w (t, r)
  have hfeature (r : Fin 2) : ∃ a : Fin m → WitnessFeature A B (W r), ∀ c d,
      witnessValue A B (W r) (a c) (restrictParam A B (p d)) =
        if c = d then 1 else 0 := by
    have hpre (v : W r) : ∃ t : OrderedPair m, w (t, r) = v.val := by
      obtain ⟨t, _, ht⟩ := Finset.mem_image.mp v.property
      exact ⟨t, ht⟩
    choose code hcode using hpre
    let loc (t : OrderedPair m) : W r := ⟨w (t, r), Finset.mem_image.mpr ⟨t, by simp, rfl⟩⟩
    have hcode_loc (t : OrderedPair m) : code (loc t) = t := by
      exact congrArg Prod.fst (hw (hcode (loc t)))
    apply exists_deltaFeature A B m (fun c => restrictParam A B (p c)) (W r)
      code loc hcode_loc
    intro v
    have h := (hfp (code v, r)).2
    change p (code v).val.1 v.val.val ≠ p (code v).val.2 v.val.val
    have hv : f (code v, r) = v.val.val := congrArg Subtype.val (hcode v)
    exact hv ▸ h
  obtain ⟨a1, ha1⟩ := hfeature 0
  obtain ⟨a2, ha2⟩ := hfeature 1
  refine ⟨W 0, W 1, ?_, a1, a2, fun c d => ⟨ha1 c d, ha2 c d⟩⟩
  apply Finset.disjoint_left.mpr
  intro n hn0 hn1
  obtain ⟨t, _, ht⟩ := Finset.mem_image.mp hn0
  obtain ⟨u, _, hu⟩ := Finset.mem_image.mp hn1
  have h := congrArg Prod.snd (hw (ht.trans hu.symm))
  exact (by decide : (0 : Fin 2) ≠ 1) h


end NoUniversalFSigma.Proof.Packet
