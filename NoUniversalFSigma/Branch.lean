module

public import NoUniversalFSigma.BranchBasic
public import NoUniversalFSigma.Hilbert

@[expose] public section

/-! # Topological and algebraic properties of the branch family -/

noncomputable section

open Set Filter Topology
open scoped ENNReal lp

namespace NoUniversalFSigma.Proof.Branch

lemma continuous_nodePrefix (n : ℕ) : Continuous fun x : Point => nodePrefix x n := by
  exact continuous_sigmaMk.comp (continuous_pi fun i : Fin n => continuous_apply (i : ℕ))

lemma isLocallyConstant_term (n : ℕ) : IsLocallyConstant fun x : Point => term x n := by
  have h : IsLocallyConstant fun x : Point => (nodePrefix x n, x n) :=
    (IsLocallyConstant.iff_continuous _).2 ((continuous_nodePrefix n).prodMk (continuous_apply n))
  exact h.comp fun p : Node × ℕ =>
    (lp.single 2 (p.1, none) (weight p.1) +
      lp.single 2 (p.1, some (p.2 / 2)) (weight p.1 * sign p.2) : Space)

lemma continuous_j : Continuous j := by
  exact continuous_tsum (fun n => (isLocallyConstant_term n).continuous)
    ((summable_geometric_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 4)
      (by norm_num : (1 / 4 : ℝ) < 1)).mul_left 2)
    (fun n x => norm_term_le_geometric x n)

lemma isLocallyConstant_coordinate (c : Coord) : IsLocallyConstant fun x => j x c := by
  have h := (isLocallyConstant_term c.1.1).comp (fun b : Space => b c)
  simpa only [Function.comp_def, ← j_apply] using h

lemma j_injective : Function.Injective j := by
  intro x y h
  funext n
  have hm : j y (nodePrefix x (n + 1), none) = weight (nodePrefix x (n + 1)) := by
    rw [← h, j_marker]
    simp only [nodePrefix, ↓reduceIte]
  have hp : nodePrefix y (n + 1) = nodePrefix x (n + 1) := by
    by_contra hn
    rw [j_marker] at hm
    simp only [nodePrefix_fst] at hm
    simp [hn] at hm
    exact weight_ne_zero _ hm.symm
  exact (((nodePrefix_eq_iff y (nodePrefix x (n + 1))).1 hp) ⟨n, by change n < n + 1; omega⟩).symm

/-- The empty-node marker is the mass coordinate. -/
lemma j_mass (x : Point) : j x (nodePrefix (fun _ => 0) 0, none) = 1 := by
  rw [j_marker]
  have h : nodePrefix x 0 = nodePrefix (fun _ => 0) 0 := by
    apply (nodePrefix_eq_iff x (nodePrefix (fun _ => 0) 0)).2
    intro i
    exact Fin.elim0 i
  simp [h]

lemma coordinates_separate {x y : Point} (h : ∀ c : Coord, j x c = j y c) : x = y :=
  j_injective (lp.ext (funext h))

/-- The real algebraic span, without taking topological closure. -/
def span : Submodule ℝ Space := Submodule.span ℝ (range j)

lemma digit_eq_of_code_eq {k l : ℕ} (hd : k / 2 = l / 2) (hs : sign k = sign l) : k = l := by
  unfold sign at hs
  split_ifs at hs with hk hl <;> norm_num at hs <;> omega

lemma one_le_abs_sign_sub {k l : ℕ} (hd : k / 2 = l / 2) (hne : k ≠ l) :
    1 ≤ |sign k - sign l| := by
  have hs : sign k ≠ sign l := fun h => hne (digit_eq_of_code_eq hd h)
  unfold sign at hs ⊢
  by_cases hk : k % 2 = 0 <;> by_cases hl : l % 2 = 0 <;> simp_all <;> norm_num at *

lemma weight_le_dist_of_digit_ne {x y : Point} (n : ℕ)
    (hp : nodePrefix x n = nodePrefix y n) (hne : x n ≠ y n) :
    weight (nodePrefix x n) ≤ dist (j x) (j y) := by
  let s := nodePrefix x n
  let c : Coord := (s, some (x n / 2))
  have hx : j x c = weight s * sign (x n) := by
    dsimp [c, s]
    rw [j_signed]
    simp
  have hpre : nodePrefix y n = s := hp.symm
  by_cases hd : y n / 2 = x n / 2
  · have hy : j y c = weight s * sign (y n) := by
      dsimp [c, s]
      rw [j_signed]
      simp [hpre, hd, s]
    calc
      weight s ≤ weight s * |sign (x n) - sign (y n)| := by
        exact le_mul_of_one_le_right (weight_pos s).le (one_le_abs_sign_sub hd.symm hne)
      _ = ‖(j x - j y) c‖ := by
        change _ = ‖j x c - j y c‖
        rw [hx, hy, ← mul_sub, Real.norm_eq_abs, abs_mul, abs_of_pos (weight_pos s)]
      _ ≤ ‖j x - j y‖ := lp.norm_apply_le_norm (by norm_num) _ c
      _ = dist (j x) (j y) := (dist_eq_norm _ _).symm
  · have hy : j y c = 0 := by
      dsimp [c, s]
      rw [j_signed]
      simp [hpre, hd, s]
    calc
      weight s = ‖(j x - j y) c‖ := by
        change _ = ‖j x c - j y c‖
        rw [hx, hy, sub_zero, Real.norm_eq_abs, abs_mul, abs_sign,
          abs_of_pos (weight_pos s), mul_one]
      _ ≤ ‖j x - j y‖ := lp.norm_apply_le_norm (by norm_num) _ c
      _ = dist (j x) (j y) := (dist_eq_norm _ _).symm

lemma eventually_digit_of_cauchy (u : ℕ → Point) (hu : CauchySeq fun m => j (u m))
    (n : ℕ) (x : Point) (hx : ∀ᶠ m in atTop, nodePrefix (u m) n = nodePrefix x n) :
    ∃ d : ℕ, ∀ᶠ m in atTop, u m n = d := by
  obtain ⟨M, hM⟩ := eventually_atTop.1 hx
  obtain ⟨N, hN⟩ := Metric.cauchySeq_iff.1 hu (weight (nodePrefix x n)) (weight_pos _)
  let K := max M N
  refine ⟨u K n, eventually_atTop.2 ⟨K, fun m hm => ?_⟩⟩
  by_contra hne
  have hp : nodePrefix (u m) n = nodePrefix (u K) n :=
    (hM m (le_trans (le_max_left _ _) hm)).trans (hM K (le_max_left _ _)).symm
  have hgap := weight_le_dist_of_digit_ne n hp hne
  rw [hM m (le_trans (le_max_left _ _) hm)] at hgap
  exact (not_lt_of_ge hgap) (hN m (le_trans (le_max_right _ _) hm) K (le_max_right _ _))

lemma eventually_prefix_of_cauchy (u : ℕ → Point) (hu : CauchySeq fun m => j (u m)) (n : ℕ) :
    ∃ x : Point, ∀ᶠ m in atTop, nodePrefix (u m) n = nodePrefix x n := by
  induction n with
  | zero =>
    refine ⟨fun _ => 0, Eventually.of_forall fun m => ?_⟩
    apply (nodePrefix_eq_iff (u m) (nodePrefix (fun _ => 0) 0)).2
    intro i
    exact Fin.elim0 i
  | succ n ih =>
    obtain ⟨x, hx⟩ := ih
    obtain ⟨d, hd⟩ := eventually_digit_of_cauchy u hu n x hx
    obtain ⟨M, hM⟩ := eventually_atTop.1 (hx.and hd)
    refine ⟨u M, eventually_atTop.2 ⟨M, fun m hm => ?_⟩⟩
    apply (nodePrefix_eq_iff (u m) (nodePrefix (u M) (n + 1))).2
    intro i
    change u m (i : ℕ) = u M (i : ℕ)
    have hi : (i : ℕ) < n + 1 := i.2
    by_cases hin : (i : ℕ) < n
    · have hem := ((nodePrefix_eq_iff (u m) (nodePrefix x n)).1 (hM m hm).1) ⟨i, hin⟩
      have heM := ((nodePrefix_eq_iff (u M) (nodePrefix x n)).1 (hM M le_rfl).1) ⟨i, hin⟩
      exact hem.trans heM.symm
    · have hin' : (i : ℕ) = n := by omega
      simpa only [hin'] using (hM m hm).2.trans (hM M le_rfl).2.symm

/-- Hilbert-Cauchy branch vectors have a convergent sequence of labels. -/
lemma exists_tendsto_of_cauchy (u : ℕ → Point) (hu : CauchySeq fun m => j (u m)) :
    ∃ x : Point, Tendsto u atTop (𝓝 x) := by
  have hd : ∀ n : ℕ, ∃ d : ℕ, ∀ᶠ m in atTop, u m n = d := by
    intro n
    obtain ⟨x, hx⟩ := eventually_prefix_of_cauchy u hu n
    exact eventually_digit_of_cauchy u hu n x hx
  choose x hx using hd
  refine ⟨x, tendsto_pi_nhds.2 fun n => ?_⟩
  exact tendsto_const_nhds.congr' ((hx n).mono fun _ h => h.symm)

lemma isClosedMap_j : IsClosedMap j := by
  intro A hA
  apply isSeqClosed_iff_isClosed.1
  intro v b hv hb
  choose u hu hju using hv
  have hj : Tendsto (fun m => j (u m)) atTop (𝓝 b) := by simpa only [hju] using hb
  obtain ⟨x, hx⟩ := exists_tendsto_of_cauchy u hj.cauchySeq
  refine ⟨x, hA.mem_of_tendsto hx (Eventually.of_forall hu), ?_⟩
  exact tendsto_nhds_unique ((continuous_j.tendsto x).comp hx) hj

lemma isClosedEmbedding_j : IsClosedEmbedding j :=
  IsClosedEmbedding.of_continuous_injective_isClosedMap continuous_j j_injective isClosedMap_j

lemma eventually_nodePrefix_ne {x y : Point} (hxy : x ≠ y) :
    ∀ᶠ n : ℕ in atTop, nodePrefix x n ≠ nodePrefix y n := by
  obtain ⟨k, hk⟩ : ∃ k, x k ≠ y k := by
    by_contra h
    push Not at h
    exact hxy (funext h)
  refine eventually_atTop.2 ⟨k + 1, fun n hn he => ?_⟩
  have he' := ((nodePrefix_eq_iff x (nodePrefix y n)).1 he) ⟨k, by change k < n; omega⟩
  exact hk he'

lemma eventually_nodePrefix_injOn (S : Finset Point) :
    ∀ᶠ n : ℕ in atTop, Set.InjOn (fun x => nodePrefix x n) S := by
  classical
  have h : ∀ᶠ n : ℕ in atTop, ∀ x ∈ S, ∀ y ∈ S, x ≠ y → nodePrefix x n ≠ nodePrefix y n := by
    refine (S.eventually_all).2 fun x hx => (S.eventually_all).2 fun y hy => ?_
    by_cases hxy : x = y
    · exact Eventually.of_forall fun _ h => (h hxy).elim
    · exact (eventually_nodePrefix_ne hxy).mono fun _ h _ => h
  exact h.mono fun _ hn x hx y hy he => by
    by_contra hxy
    exact hn x hx y hy hxy he

lemma sum_marker (S : Finset Point) (a : Point → ℝ) (n : ℕ)
    (hn : Set.InjOn (fun x => nodePrefix x n) S) (x : Point) (hx : x ∈ S) :
    (∑ y ∈ S, a y • j y) (nodePrefix x n, none) = a x * weight (nodePrefix x n) := by
  classical
  simp only [lp.coeFn_sum, Finset.sum_apply, lp.coeFn_smul, Pi.smul_apply, smul_eq_mul]
  rw [Finset.sum_eq_single x]
  · rw [j_marker]
    simp
  · intro y hy hne
    have hp : nodePrefix y n ≠ nodePrefix x n := fun h => hne (hn hy hx h)
    rw [j_marker]
    simp [hp]
  · exact fun h => (h hx).elim

lemma linearIndependent_j : LinearIndependent ℝ j := by
  classical
  apply linearIndependent_iff'.2
  intro S a hsum x hx
  obtain ⟨n, hn⟩ := (eventually_nodePrefix_injOn S).exists
  have he := congrArg (fun b : Space => b (nodePrefix x n, none)) hsum
  rw [sum_marker S a n hn x hx] at he
  change a x * weight (nodePrefix x n) = 0 at he
  exact (mul_eq_zero.1 he).resolve_right (weight_ne_zero _)

lemma eq_zero_of_mem_span_finite_support {b : Space} (hb : b ∈ span)
    (hfinite : (Function.support fun c : Coord => b c).Finite) : b = 0 := by
  classical
  obtain ⟨a, ha⟩ := (Finsupp.mem_span_range_iff_exists_finsupp).1 hb
  by_contra hb0
  have ha0 : a ≠ 0 := by
    intro h
    simp [h] at ha
    exact hb0 ha.symm
  obtain ⟨x, hx⟩ : ∃ x, a x ≠ 0 := by
    simpa only [ne_eq, Finsupp.ext_iff, Finsupp.zero_apply, not_forall] using ha0
  have hxS : x ∈ a.support := Finsupp.mem_support_iff.2 hx
  obtain ⟨L, hL⟩ := eventually_atTop.1 (eventually_nodePrefix_injOn a.support)
  have hnonzero : ∀ n : ℕ, b (nodePrefix x (n + L), none) ≠ 0 := by
    intro n
    rw [← ha]
    change (∑ y ∈ a.support, a y • j y) (nodePrefix x (n + L), none) ≠ 0
    rw [sum_marker a.support a (n + L) (hL _ (by omega)) x hxS]
    exact mul_ne_zero hx (weight_ne_zero _)
  have hinj : Function.Injective (fun n : ℕ => ((nodePrefix x (n + L), none) : Coord)) := by
    intro n m h
    have he := congrArg (fun c : Coord => c.1.1) h
    simp only [nodePrefix_fst] at he
    omega
  have hi := Set.infinite_range_of_injective hinj
  apply hi
  apply hfinite.subset
  rintro c ⟨n, rfl⟩
  exact hnonzero n

/-- Extend a node by one prescribed digit, followed by zeroes. -/
def extend (s : Node) (k : ℕ) : Point := fun n =>
  if h : n < s.1 then s.2 ⟨n, h⟩ else if n = s.1 then k else 0

@[simp] lemma nodePrefix_extend (s : Node) (k : ℕ) : nodePrefix (extend s k) s.1 = s := by
  apply (nodePrefix_eq_iff _ s).2
  intro i
  simp [extend, i.2]

@[simp] lemma extend_digit (s : Node) (k : ℕ) : extend s k s.1 = k := by simp [extend]

lemma nodePrefix_eq_of_agree (x y : Point) (n : ℕ) (h : ∀ k < n, x k = y k) :
    nodePrefix x n = nodePrefix y n := by
  apply (nodePrefix_eq_iff x (nodePrefix y n)).2
  intro i
  exact h i i.2

lemma term_eq_of_agree (x y : Point) (n : ℕ) (h : ∀ k ≤ n, x k = y k) : term x n = term y n := by
  have hp := nodePrefix_eq_of_agree x y n (fun k hk => h k hk.le)
  simp only [term, hp, h n le_rfl]

/-- The fixed finite prefix vector attached to `s`. -/
def prefixVector (s : Node) : Space := ∑ n ∈ Finset.range s.1, term (extend s 0) n

lemma initial_eq_prefixVector {s : Node} {x : Point} (hx : x ∈ Cylinder s) :
    (∑ n ∈ Finset.range s.1, term x n) = prefixVector s := by
  apply Finset.sum_congr rfl
  intro n hn
  apply term_eq_of_agree
  intro k hk
  have hks : k < s.1 := lt_of_le_of_lt hk (Finset.mem_range.1 hn)
  have h := ((nodePrefix_eq_iff x s).1 hx) ⟨k, hks⟩
  simpa only [extend, dite_eq_left hks] using h

lemma j_eq_prefixVector_add_tail {s : Node} {x : Point} (hx : x ∈ Cylinder s) :
    j x = prefixVector s + tail x s.1 := by
  rw [← initial_add_tail, initial_eq_prefixVector hx]

lemma isClosed_cylinder (s : Node) : IsClosed (Cylinder s) :=
  isClosed_eq (continuous_nodePrefix s.1) continuous_const

lemma isClosed_tail_image (s : Node) : IsClosed ((fun x => tail x s.1) '' Cylinder s) := by
  have he : ((fun x => tail x s.1) '' Cylinder s) =
      (fun b : Space => prefixVector s + b) ⁻¹' (j '' Cylinder s) := by
    ext b
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact ⟨x, hx, (j_eq_prefixVector_add_tail hx)⟩
    · rintro ⟨x, hx, hb⟩
      refine ⟨x, hx, ?_⟩
      have h := (j_eq_prefixVector_add_tail hx).symm.trans hb
      exact add_left_cancel h
  rw [he]
  exact (isClosedMap_j _ (isClosed_cylinder s)).preimage (continuous_const.add continuous_id)

/-- The first node is an initial segment of the second node. -/
def NodeExtends (s t : Node) : Prop :=
  ∃ h : s.1 ≤ t.1, ∀ i : Fin s.1, t.2 (i.castLE h) = s.2 i

def DescendantCoords (s : Node) : Set Coord := {c | NodeExtends s c.1}

lemma nodePrefix_extends_iff {s : Node} {x : Point} (hx : x ∈ Cylinder s) (n : ℕ) :
    NodeExtends s (nodePrefix x n) ↔ s.1 ≤ n := by
  constructor
  · rintro ⟨h, _⟩
    exact h
  · intro h
    refine ⟨h, fun i => ?_⟩
    exact ((nodePrefix_eq_iff x s).1 hx) i

lemma j_apply_eq_zero_of_not_prefix (x : Point) (c : Coord)
    (h : nodePrefix x c.1.1 ≠ c.1) : j x c = 0 := by
  rcases c with ⟨s, k⟩
  cases k with
  | none => simp only [j_marker, ite_eq_right h]
  | some k => simp [j_signed, h]

lemma mask_j_eq_tail {s : Node} {x : Point} (hx : x ∈ Cylinder s) :
    hilbertMask (DescendantCoords s) (j x) = tail x s.1 := by
  apply lp.ext
  funext c
  rw [hilbertMask_apply, tail_apply]
  by_cases hp : nodePrefix x c.1.1 = c.1
  · have he : c ∈ DescendantCoords s ↔ s.1 ≤ c.1.1 := by
      change NodeExtends s c.1 ↔ _
      rw [← hp]
      exact nodePrefix_extends_iff hx _
    simp only [he]
  · rw [j_apply_eq_zero_of_not_prefix x c hp]
    split_ifs <;> rfl

lemma nodePrefix_eq_of_extends {s t : Node} {x : Point}
    (h : NodeExtends s t) (hx : nodePrefix x t.1 = t) : nodePrefix x s.1 = s := by
  obtain ⟨h, ht⟩ := h
  apply (nodePrefix_eq_iff x s).2
  intro i
  exact (((nodePrefix_eq_iff x t).1 hx) (i.castLE h)).trans (ht i)

lemma mask_j_eq_zero {s : Node} {x : Point} (hx : nodePrefix x s.1 ≠ s) :
    hilbertMask (DescendantCoords s) (j x) = 0 := by
  classical
  apply lp.ext
  funext c
  rw [hilbertMask_apply]
  change (if c ∈ DescendantCoords s then j x c else 0) = 0
  split_ifs with h
  · exact j_apply_eq_zero_of_not_prefix x c (fun he => hx (nodePrefix_eq_of_extends h he))
  · rfl

lemma finite_support_single (c : Coord) (r : ℝ) :
    Function.HasFiniteSupport fun d => (lp.single 2 c r : Space) d := by
  apply (Set.finite_singleton c).subset
  intro d hd
  by_contra hdc
  have he : d ≠ c := fun h => hdc (Set.mem_singleton_iff.2 h)
  simp [Function.mem_support, lp.single_apply, Pi.single_apply, he] at hd

lemma finite_support_term (x : Point) (n : ℕ) :
    Function.HasFiniteSupport fun c => term x n c := by
  exact (finite_support_single _ _).add (finite_support_single _ _)

lemma finite_support_prefixVector (s : Node) :
    Function.HasFiniteSupport fun c => prefixVector s c := by
  simpa only [prefixVector, lp.coeFn_sum, Finset.sum_apply] using
    Function.HasFiniteSupport.sum (finite_support_term (extend s 0)) (Finset.range s.1)

lemma finite_support_smul (r : ℝ) {b : Space}
    (hb : Function.HasFiniteSupport fun c => b c) :
    Function.HasFiniteSupport fun c => (r • b) c := by
  exact hb.subset (Function.support_smul_subset_right (fun _ : Coord => r) (fun c => b c))

lemma prefixVector_marker (s : Node) : prefixVector s (s, none) = 0 := by
  simp only [prefixVector, lp.coeFn_sum, Finset.sum_apply]
  apply Finset.sum_eq_zero
  intro n hn
  exact term_apply_of_ne_level _ n (s, none) (Nat.ne_of_lt (Finset.mem_range.1 hn))

/-- The nonzero finite-support limit of the sums of paired branches. -/
def escapeVector (s : Node) : Space :=
  (2 : ℝ) • prefixVector s + (2 : ℝ) • lp.single 2 (s, none) (weight s)

lemma escapeVector_marker (s : Node) : escapeVector s (s, none) = 2 * weight s := by
  change 2 * prefixVector s (s, none) +
    2 * (lp.single 2 (s, none) (weight s) : Space) (s, none) = _
  rw [prefixVector_marker]
  simp [lp.single_apply]

lemma escapeVector_ne_zero (s : Node) : escapeVector s ≠ 0 := by
  intro h
  have he := congrArg (fun b : Space => b (s, none)) h
  rw [escapeVector_marker] at he
  change 2 * weight s = 0 at he
  exact (mul_ne_zero (by norm_num) (weight_ne_zero s)) he

lemma escapeVector_not_mem_span (s : Node) : escapeVector s ∉ span := by
  intro h
  have hfinite : Function.HasFiniteSupport fun c => escapeVector s c :=
    (finite_support_smul 2 (finite_support_prefixVector s)).add
      (finite_support_smul 2 (finite_support_single _ _))
  exact escapeVector_ne_zero s (eq_zero_of_mem_span_finite_support h hfinite)

lemma norm_tail_extend_le (s : Node) (k : ℕ) :
    ‖tail (extend s k) (s.1 + 1)‖ ≤ (8 / 3 : ℝ) * weight s * (1 / 2 : ℝ) ^ (k + 2) := by
  simpa only [weight_nodePrefix_succ, nodePrefix_extend, extend_digit, mul_assoc] using
    norm_tail_le (extend s k) (s.1 + 1)

lemma even_digit_pow (n : ℕ) : (1 / 2 : ℝ) ^ (2 * n + 2) = (1 / 4 : ℝ) ^ (n + 1) := by
  rw [show 2 * n + 2 = 2 * (n + 1) by omega, pow_mul]
  norm_num

lemma paired_terms (s : Node) (n : ℕ) :
    term (extend s (2 * n)) s.1 + term (extend s (2 * n + 1)) s.1 =
      (2 : ℝ) • lp.single 2 (s, none) (weight s) := by
  have hdiv0 : 2 * n / 2 = n := by omega
  have hdiv1 : (2 * n + 1) / 2 = n := by omega
  have hsign0 : sign (2 * n) = 1 := by simp [sign]
  have hsign1 : sign (2 * n + 1) = -1 := by simp [sign]
  simp only [term, nodePrefix_extend, extend_digit, hdiv0, hdiv1, hsign0, hsign1,
    mul_one, mul_neg_one, lp.single_neg]
  module

lemma paired_branches_eq (s : Node) (n : ℕ) :
    j (extend s (2 * n)) + j (extend s (2 * n + 1)) =
      escapeVector s + tail (extend s (2 * n)) (s.1 + 1) +
        tail (extend s (2 * n + 1)) (s.1 + 1) := by
  have he (k : ℕ) : j (extend s k) = prefixVector s + term (extend s k) s.1 +
      tail (extend s k) (s.1 + 1) := by
    rw [← initial_add_tail _ (s.1 + 1), Finset.sum_range_succ,
      initial_eq_prefixVector (show extend s k ∈ Cylinder s from nodePrefix_extend s k)]
  rw [he, he]
  unfold escapeVector
  rw [← paired_terms s n]
  module

lemma tendsto_paired_branches (s : Node) :
    Tendsto (fun n : ℕ => j (extend s (2 * n)) + j (extend s (2 * n + 1))) atTop
      (𝓝 (escapeVector s)) := by
  have hbound0 (n : ℕ) : ‖tail (extend s (2 * n)) (s.1 + 1)‖ ≤
      ((8 / 3 : ℝ) * weight s / 4) * (1 / 4 : ℝ) ^ n := by
    have h := norm_tail_extend_le s (2 * n)
    rw [even_digit_pow, pow_succ] at h
    convert h using 1; ring
  have hbound1 (n : ℕ) : ‖tail (extend s (2 * n + 1)) (s.1 + 1)‖ ≤
      ((8 / 3 : ℝ) * weight s / 4) * (1 / 4 : ℝ) ^ n := by
    have h := norm_tail_extend_le s (2 * n + 1)
    have hp : (1 / 2 : ℝ) ^ (2 * n + 1 + 2) = (1 / 2 : ℝ) * (1 / 4 : ℝ) ^ (n + 1) := by
      rw [show 2 * n + 1 + 2 = (2 * n + 2) + 1 by omega, pow_succ, even_digit_pow]
      ring
    rw [hp, pow_succ] at h
    have hw := weight_pos s
    have hg : 0 ≤ (1 / 4 : ℝ) ^ n := by positivity
    nlinarith
  have hgeom : Tendsto (fun n : ℕ => ((8 / 3 : ℝ) * weight s / 4) * (1 / 4 : ℝ) ^ n)
      atTop (𝓝 0) := by
    simpa using tendsto_const_nhds.mul
      (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 4)
        (by norm_num : (1 / 4 : ℝ) < 1))
  have ht0 : Tendsto (fun n : ℕ => tail (extend s (2 * n)) (s.1 + 1)) atTop (𝓝 0) := by
    exact tendsto_zero_iff_norm_tendsto_zero.2 (squeeze_zero (fun _ => norm_nonneg _) hbound0 hgeom)
  have ht1 : Tendsto (fun n : ℕ => tail (extend s (2 * n + 1)) (s.1 + 1)) atTop (𝓝 0) := by
    exact tendsto_zero_iff_norm_tendsto_zero.2 (squeeze_zero (fun _ => norm_nonneg _) hbound1 hgeom)
  have ht := ((tendsto_const_nhds (x := escapeVector s)).add ht0).add ht1
  simpa only [paired_branches_eq, add_zero] using ht

/-- Every cylinder admits paired branch sums converging outside the algebraic span. -/
theorem escape_cylinder (s : Node) :
    ∃ z : Space, z ∉ span ∧
      ∃ x y : ℕ → Point, (∀ n, x n ∈ Cylinder s ∧ y n ∈ Cylinder s) ∧
        Tendsto (fun n => j (x n) + j (y n)) atTop (𝓝 z) := by
  exact ⟨escapeVector s, escapeVector_not_mem_span s, fun n => extend s (2 * n),
    fun n => extend s (2 * n + 1), fun n => ⟨nodePrefix_extend s _, nodePrefix_extend s _⟩,
    tendsto_paired_branches s⟩

end NoUniversalFSigma.Proof.Branch
