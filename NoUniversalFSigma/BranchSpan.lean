module

public import NoUniversalFSigma.Branch
public import NoUniversalFSigma.SpanCharts
public import NoUniversalFSigma.BorelHierarchy

@[expose] public section

/-! # A countable closed cover of the algebraic branch span -/

noncomputable section

open Set Filter Topology NoUniversalFSigma
open scoped lp

namespace NoUniversalFSigma.Proof.Branch

/-- The normalized marker coordinate recovers a branch coefficient. -/
def coefficient (s : Node) : Space →L[ℝ] ℝ :=
  (weight s)⁻¹ • lp.evalCLM ℝ (fun _ : Coord => ℝ) 2 (s, none)

lemma coefficient_j (s : Node) (x : Point) :
    coefficient s (j x) = if nodePrefix x s.1 = s then 1 else 0 := by
  change (weight s)⁻¹ * j x (s, none) = _
  rw [j_marker]
  split_ifs <;> simp [weight_ne_zero]

/-- Recover every coefficient and scaled tail in a chart with distinct equal-level prefixes. -/
lemma recover_finiteBranchChart {r : ℕ} (p : Fin r → Node) (L : ℕ)
    (hlevel : ∀ i, (p i).1 = L) (hinj : Function.Injective p)
    (a : Fin r → ℝ) (t : Fin r → Space)
    (ht : ∀ i, t i ∈ (fun x => tail x (p i).1) '' Cylinder (p i)) :
    (∀ s, coefficient (p s) (∑ i, a i • (prefixVector (p i) + t i)) = a s) ∧
    (∀ s, hilbertMask (DescendantCoords (p s))
      (∑ i, a i • (prefixVector (p i) + t i)) = a s • t s) := by
  choose x hx hxt using ht
  have hrepr (i : Fin r) : prefixVector (p i) + t i = j (x i) := by
    rw [← hxt i, ← j_eq_prefixVector_add_tail (hx i)]
  have hother (i s : Fin r) (hne : i ≠ s) : nodePrefix (x i) (p s).1 ≠ p s := by
    have hlen : (p s).1 = (p i).1 := (hlevel s).trans (hlevel i).symm
    rw [hlen, hx i]
    exact fun h => hne (hinj h)
  have hcoeff (i s : Fin r) : coefficient (p s) (j (x i)) = if i = s then 1 else 0 := by
    by_cases his : i = s
    · subst i
      have hxs : nodePrefix (x s) (p s).1 = p s := hx s
      simp only [coefficient_j, hxs, ↓reduceIte]
    · simp only [coefficient_j, ite_eq_right (hother i s his), ite_eq_right his]
  have hproj (i s : Fin r) : hilbertMask (DescendantCoords (p s)) (j (x i)) =
      if i = s then t i else 0 := by
    by_cases his : i = s
    · subst i
      simpa using (mask_j_eq_tail (hx s)).trans (hxt s)
    · rw [mask_j_eq_zero (hother i s his)]
      simp [his]
  constructor
  · intro s
    calc
      coefficient (p s) (∑ i, a i • (prefixVector (p i) + t i)) =
          ∑ i, a i • coefficient (p s) (j (x i)) := by simp only [hrepr, map_sum, map_smul]
      _ = a s := by simp [hcoeff]
  · intro s
    calc
      hilbertMask (DescendantCoords (p s)) (∑ i, a i • (prefixVector (p i) + t i)) =
          ∑ i, a i • hilbertMask (DescendantCoords (p s)) (j (x i)) := by
        simp only [hrepr, map_sum, map_smul]
      _ = a s • t s := by simp [hproj, smul_ite]

/-- A bounded-coefficient finite sum chart for prescribed branch prefixes. -/
def finiteBranchChart {r : ℕ} (p : Fin r → Node) (k : ℕ) : Set Space :=
  finiteSpanChart (fun i => prefixVector (p i))
    (fun i => (fun x => tail x (p i).1) '' Cylinder (p i)) (1 / (k + 1 : ℝ)) (k + 1)

lemma isClosed_finiteBranchChart {r : ℕ} (p : Fin r → Node) (L : ℕ)
    (hlevel : ∀ i, (p i).1 = L) (hinj : Function.Injective p) (k : ℕ) :
    IsClosed (finiteBranchChart p k) := by
  apply isClosed_finiteSpanChart _ _ _ _ (by positivity) (fun i => isClosed_tail_image (p i))
    (fun i => coefficient (p i)) (fun i => hilbertMask (DescendantCoords (p i)))
  · intro a t ht
    exact (recover_finiteBranchChart p L hlevel hinj a t ht).1
  · intro a t ht
    exact (recover_finiteBranchChart p L hlevel hinj a t ht).2

/-- The discrete data specifying one closed branch-span chart. -/
structure SpanChartIndex where
  size : ℕ
  level : ℕ
  nodes : Fin size → Node
  bound : ℕ
  deriving Countable

/-- Invalid prefix tuples contribute the empty closed set. -/
def spanChart (d : SpanChartIndex) : Set Space :=
  {b | ((∀ i, (d.nodes i).1 = d.level) ∧ Function.Injective d.nodes) ∧
    b ∈ finiteBranchChart d.nodes d.bound}

lemma isClosed_spanChart (d : SpanChartIndex) : IsClosed (spanChart d) := by
  by_cases h : (∀ i, (d.nodes i).1 = d.level) ∧ Function.Injective d.nodes
  · simpa [spanChart, h] using
      isClosed_finiteBranchChart d.nodes d.level h.1 h.2 d.bound
  · simp [spanChart, h]

lemma spanChart_subset_span (d : SpanChartIndex) : spanChart d ⊆ span := by
  rintro b ⟨_, a, t, _, ht, rfl⟩
  apply Submodule.sum_mem
  intro i _
  apply Submodule.smul_mem
  obtain ⟨x, hx, hxt⟩ := ht i
  rw [← hxt, ← j_eq_prefixVector_add_tail hx]
  exact Submodule.subset_span ⟨x, rfl⟩

/-- Finitely many nonzero real coefficients fit a common reciprocal/integer annulus. -/
lemma exists_uniform_annulus {r : ℕ} (a : Fin r → ℝ) (ha : ∀ i, a i ≠ 0) :
    ∃ k : ℕ, ∀ i, 1 / (k + 1 : ℝ) ≤ |a i| ∧ |a i| ≤ k + 1 := by
  have h (i : Fin r) : ∀ᶠ k : ℕ in atTop,
      1 / (k + 1 : ℝ) ≤ |a i| ∧ |a i| ≤ k + 1 := by
    obtain ⟨n, hn⟩ := exists_nat_one_div_lt (abs_pos.mpr (ha i))
    obtain ⟨m, hm⟩ := exists_nat_gt |a i|
    refine eventually_atTop.2 ⟨max n m, fun k hk => ⟨?_, ?_⟩⟩
    · apply le_trans _ hn.le
      apply one_div_le_one_div_of_le (by positivity)
      have hnk : n ≤ k := le_trans (le_max_left _ _) hk
      exact_mod_cast Nat.add_le_add_right hnk 1
    · apply hm.le.trans
      have hmk : m ≤ k + 1 := by omega
      exact_mod_cast hmk
  exact (Filter.eventually_all.2 h).exists

lemma mem_iUnion_spanChart {b : Space} (hb : b ∈ span) : b ∈ ⋃ d, spanChart d := by
  obtain ⟨a, ha⟩ := Finsupp.mem_span_range_iff_exists_finsupp.mp hb
  change (∑ x ∈ a.support, a x • j x) = b at ha
  let r := Fintype.card a.support
  let e : Fin r ≃ a.support := (Fintype.equivFin a.support).symm
  let x : Fin r → Point := fun i => (e i).1
  let c : Fin r → ℝ := fun i => a (x i)
  obtain ⟨L, hL⟩ := (eventually_nodePrefix_injOn a.support).exists
  let p : Fin r → Node := fun i => nodePrefix (x i) L
  have hp : Function.Injective p := by
    intro i l h
    apply e.injective
    apply Subtype.ext
    exact hL (e i).2 (e l).2 h
  have hc : ∀ i, c i ≠ 0 := fun i => Finsupp.mem_support_iff.mp (e i).2
  obtain ⟨k, hk⟩ := exists_uniform_annulus c hc
  let d : SpanChartIndex := ⟨r, L, p, k⟩
  apply mem_iUnion.mpr
  refine ⟨d, ⟨fun _ => rfl, hp⟩, c, (fun i => tail (x i) L), hk, ?_, ?_⟩
  · intro i
    exact ⟨x i, rfl, rfl⟩
  · have hsum : (∑ i : Fin r, c i • j (x i)) = ∑ y : a.support, a y.1 • j y.1 :=
      Fintype.sum_equiv e _ _ (fun _ => rfl)
    rw [← Finset.sum_coe_sort a.support] at ha
    calc
      b = ∑ i : Fin r, c i • j (x i) := ha.symm.trans hsum.symm
      _ = ∑ i : Fin r, c i • (prefixVector (p i) + tail (x i) L) := by
        apply Finset.sum_congr rfl
        intro i _
        rw [j_eq_prefixVector_add_tail (show x i ∈ Cylinder (p i) from rfl)]
        rfl

/-- The branch span is the union of its countably many closed charts. -/
lemma span_eq_iUnion_spanChart : (span : Set Space) = ⋃ d, spanChart d := by
  ext b
  exact ⟨mem_iUnion_spanChart, fun hb =>
    let ⟨d, hd⟩ := mem_iUnion.mp hb
    spanChart_subset_span d hd⟩

/-- The algebraic branch span is `Fσ` in the Hilbert norm topology. -/
theorem isSigma02_span : IsSigma02 (span : Set Space) := by
  have : Nonempty SpanChartIndex := ⟨⟨0, 0, Fin.elim0, 0⟩⟩
  obtain ⟨e, he⟩ := exists_surjective_nat SpanChartIndex
  refine ⟨fun n => spanChart (e n), fun n => isClosed_spanChart (e n), ?_⟩
  rw [span_eq_iUnion_spanChart]
  exact (Function.Surjective.iUnion_comp he spanChart).symm

end NoUniversalFSigma.Proof.Branch
