module

public import NoUniversalFSigma.PacketCoordinates
public import NoUniversalFSigma.LimitRank

@[expose] public section

/-! Continuous linear insertion of one Hilbert factor into a fixed tensor packet. -/

noncomputable section

namespace NoUniversalFSigma.Proof.Packet

open Set Filter Topology
open scoped lp ENNReal

attribute [local instance] Classical.propDecidable

variable (A : ℕ → AdmissibleFamily)

def insertionConstant (i : ℕ) : ℝ := max 1 ‖hilbertFinsuppFunctional (A i).mass‖

lemma insertionConstant_nonneg (i : ℕ) : 0 ≤ insertionConstant A i :=
  (by norm_num : (0 : ℝ) ≤ 1).trans (le_max_left _ _)

/-- The linear block obtained by varying the `i`-th factor and fixing the others. -/
def insertionBlock (i : ℕ) (q : Param A) (F : Finset ℕ) :
    (A i).Space →ₗ[ℝ] ℓ²(BlockCoord A F, ℝ) :=
  if hi : i ∈ F then
    ((hilbertPiMultilinear F (fun n => (A n.val).Coord)).toLinearMap
      (fun n => beta A n.val • (A n.val).j (q n.val)) ⟨i, hi⟩).comp
        (beta A i • LinearMap.id)
  else
    (LinearMap.toSpanSingleton ℝ _ (block A F q)).comp
      (hilbertFinsuppFunctional (A i).mass).toLinearMap

lemma norm_insertionBlock_le (i : ℕ) (q : Param A) (F : Finset ℕ) (v : (A i).Space) :
    ‖insertionBlock A i q F v‖ ≤ insertionConstant A i * majorant F * ‖v‖ := by
  classical
  unfold insertionBlock
  split_ifs with hi
  · let k : F := ⟨i, hi⟩
    let m := fun n : F => beta A n.val • (A n.val).j (q n.val)
    change ‖hilbertPi F (fun n => (A n.val).Coord)
      (Function.update m k (beta A i • v))‖ ≤ _
    rw [norm_hilbertPi]
    have hb (n : F) : ‖Function.update m k (beta A i • v) n‖ ≤
        Function.update (fun n : F => (1 / 2 : ℝ) ^ (n.val + 1)) k
          ((1 / 2 : ℝ) ^ (i + 1) * ‖v‖) n := by
      by_cases hn : n = k
      · subst n
        simp only [Function.update_self, norm_smul, Real.norm_eq_abs,
          abs_of_pos (beta_pos A i)]
        exact mul_le_mul_of_nonneg_right (beta_le A i) (norm_nonneg v)
      · rw [Function.update_of_ne hn, Function.update_of_ne hn]
        exact norm_scaled_atom_le A n.val q
    calc
      (∏ n : F, ‖Function.update m k (beta A i • v) n‖) ≤
          ∏ n : F, Function.update (fun n : F => (1 / 2 : ℝ) ^ (n.val + 1)) k
            ((1 / 2 : ℝ) ^ (i + 1) * ‖v‖) n :=
        Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _) (fun n _ => hb n)
      _ = majorant F * ‖v‖ := by
        rw [Finset.prod_update_of_mem (Finset.mem_univ k)]
        have he : (1 / 2 : ℝ) ^ (i + 1) *
            (∏ n ∈ Finset.univ \ {k}, (1 / 2 : ℝ) ^ (n.val + 1)) = majorant F := by
          calc
            _ = ∏ n : F, (1 / 2 : ℝ) ^ (n.val + 1) := by
              simpa only [Finset.sdiff_singleton_eq_erase] using
                Finset.mul_prod_erase Finset.univ
                  (fun n : F => (1 / 2 : ℝ) ^ (n.val + 1)) (Finset.mem_univ k)
            _ = majorant F :=
              Finset.prod_coe_sort F (fun n => (1 / 2 : ℝ) ^ (n + 1))
        rw [mul_right_comm, he]
      _ ≤ insertionConstant A i * majorant F * ‖v‖ := by
        exact mul_le_mul_of_nonneg_right
          (le_mul_of_one_le_left (majorant_nonneg F) (le_max_left _ _)) (norm_nonneg v)
  · change ‖hilbertFinsuppFunctional (A i).mass v • block A F q‖ ≤ _
    rw [norm_smul]
    calc
      ‖hilbertFinsuppFunctional (A i).mass v‖ * ‖block A F q‖ ≤
          (‖hilbertFinsuppFunctional (A i).mass‖ * ‖v‖) * majorant F :=
        mul_le_mul ((hilbertFinsuppFunctional (A i).mass).le_opNorm v)
          (norm_block_le A F q) (norm_nonneg _) (by positivity)
      _ ≤ insertionConstant A i * majorant F * ‖v‖ := by
        unfold insertionConstant
        nlinarith [mul_le_mul_of_nonneg_right
          (le_max_right 1 ‖hilbertFinsuppFunctional (A i).mass‖)
          (mul_nonneg (majorant_nonneg F) (norm_nonneg v))]



lemma insertionBlock_j (i : ℕ) (q : Param A) (F : Finset ℕ) (t : (A i).Param) :
    insertionBlock A i q F ((A i).j t) = block A F (Function.update q i t) := by
  classical
  unfold insertionBlock
  split_ifs with hi
  · change hilbertPi F (fun n => (A n.val).Coord)
      (Function.update (fun n : F => beta A n.val • (A n.val).j (q n.val))
        ⟨i, hi⟩ (beta A i • (A i).j t)) = _
    unfold block
    congr 1
    funext n
    by_cases hn : n.val = i
    · have hn' : n = (⟨i, hi⟩ : F) := Subtype.ext hn
      subst n
      simp only [Function.update_self]
    · have hn' : n ≠ (⟨i, hi⟩ : F) := fun h => hn (congrArg Subtype.val h)
      rw [Function.update_of_ne hn', Function.update_of_ne hn]
  · change hilbertFinsuppFunctional (A i).mass ((A i).j t) • block A F q = _
    rw [(A i).mass_one, one_smul]
    unfold block
    congr 1
    funext n
    have hn : n.val ≠ i := fun h => hi (h ▸ n.property)
    rw [Function.update_of_ne hn]

lemma summable_norm_insertionTerm (i : ℕ) (q : Param A) (v : (A i).Space) :
    Summable fun F => ‖hilbertSigmaInclude F (insertionBlock A i q F v)‖ := by
  apply Summable.of_nonneg_of_le (fun _ => norm_nonneg _)
    (fun F => ?_) ((summable_majorant.mul_left (insertionConstant A i)).mul_right ‖v‖)
  rw [norm_hilbertSigmaInclude]
  exact norm_insertionBlock_le A i q F v

lemma summable_insertionTerm (i : ℕ) (q : Param A) (v : (A i).Space) :
    Summable fun F => hilbertSigmaInclude F (insertionBlock A i q F v) :=
  (summable_norm_insertionTerm A i q v).of_norm

/-- Insert an arbitrary ambient vector in one factor of a fixed countable tensor packet.
For blocks not containing that factor, its mass is the required scalar. -/
def insertion (i : ℕ) (q : Param A) : (A i).Space →L[ℝ] Space A :=
  LinearMap.mkContinuous
    { toFun := fun v => ∑' F, hilbertSigmaInclude F (insertionBlock A i q F v)
      map_add' := by
        intro v w
        simp_rw [map_add]
        exact (summable_insertionTerm A i q v).tsum_add (summable_insertionTerm A i q w)
      map_smul' := by
        intro c v
        simp_rw [map_smul]
        exact (summable_insertionTerm A i q v).tsum_const_smul c }
    (insertionConstant A i * ∑' F, majorant F) (by
      intro v
      apply (norm_tsum_le_tsum_norm (summable_norm_insertionTerm A i q v)).trans
      calc
        (∑' F, ‖hilbertSigmaInclude F (insertionBlock A i q F v)‖) ≤
            ∑' F, insertionConstant A i * majorant F * ‖v‖ :=
          (summable_norm_insertionTerm A i q v).tsum_le_tsum (fun F => by
            rw [norm_hilbertSigmaInclude]
            exact norm_insertionBlock_le A i q F v)
            ((summable_majorant.mul_left (insertionConstant A i)).mul_right ‖v‖)
        _ = (insertionConstant A i * ∑' F, majorant F) * ‖v‖ := by
          rw [tsum_mul_right, tsum_mul_left])

lemma insertion_apply (i : ℕ) (q : Param A) (v : (A i).Space) (c : Coord A) :
    insertion A i q v c = insertionBlock A i q c.1 v c.2 := by
  change (lp.evalCLM ℝ (fun _ : Coord A => ℝ) 2 c)
    (∑' F, hilbertSigmaInclude F (insertionBlock A i q F v)) = _
  rw [(lp.evalCLM ℝ (fun _ : Coord A => ℝ) 2 c).map_tsum (summable_insertionTerm A i q v)]
  change (∑' F, sigmaCoordinate F (insertionBlock A i q F v) c) = _
  rw [tsum_eq_single c.1]
  · rcases c with ⟨F, c⟩
    exact sigmaCoordinate_mk _ _ _
  · intro F hF
    exact sigmaCoordinate_other F c.1 (insertionBlock A i q F v) c.2 (Ne.symm hF)

lemma insertion_j (i : ℕ) (q : Param A) (t : (A i).Param) :
    insertion A i q ((A i).j t) = j A (Function.update q i t) := by
  ext c
  rw [insertion_apply, j_apply, insertionBlock_j]

lemma insertion_singleton (i : ℕ) (q : Param A) (v : (A i).Space) (c : (A i).Coord) :
    insertion A i q v (singletonCoord A i c) = beta A i * v c := by
  rw [insertion_apply]
  change insertionBlock A i q {i} v (singletonBlockCoord A i c) = _
  unfold insertionBlock
  rw [dite_eq_left (Finset.mem_singleton_self i)]
  change (∏ n : ({i} : Finset ℕ),
    Function.update (fun n : ({i} : Finset ℕ) => beta A n.val • (A n.val).j (q n.val))
      ⟨i, Finset.mem_singleton_self i⟩ (beta A i • v) n
        (singletonBlockCoord A i c n)) = _
  rw [Finset.prod_eq_single (⟨i, Finset.mem_singleton_self i⟩ : ({i} : Finset ℕ))]
  · rw [Function.update_self]
    rfl
  · intro n _ hn
    exact (hn (Subtype.ext (Finset.mem_singleton.mp n.property))).elim
  · intro h
    exact (h (Finset.mem_univ _)).elim

@[simp] lemma recover_insertion (i : ℕ) (q : Param A) (v : (A i).Space) :
    recover A i (insertion A i q v) = v := by
  ext c
  change (beta A i)⁻¹ * insertion A i q v (singletonCoord A i c) = _
  rw [insertion_singleton, ← mul_assoc, inv_mul_cancel₀ (beta_ne_zero A i), one_mul]

/-- The concrete packet family inherits every coordinate's diagonal escape rank. -/
theorem diagonal_rank (i : ℕ) (α : Ordinal)
    (hα : ∀ t, (t, t) ∈ escapeRemainder (A i).j (A i).span.toAddSubgroup α) :
    ∀ q, (q, q) ∈ escapeRemainder (j A) (span A).toAddSubgroup α :=
  coordinate_diagonal_rank A (j A) i (insertion A i) (recover A i)
    (insertion_j A i) (fun q => recover_j A q i) (recover_insertion A i) α hα

/-- Cofinal factor ranks give the limit rank for the actual countable tensor packet. -/
theorem cofinal_rank (r : ℕ → Ordinal) (lambda : Ordinal)
    (hlambda : Order.IsSuccLimit lambda) (hr : ∀ β < lambda, ∃ i, β ≤ r i)
    (hα : ∀ i t, (t, t) ∈ escapeRemainder (A i).j (A i).span.toAddSubgroup (r i)) :
    ∀ q, (q, q) ∈ escapeRemainder (j A) (span A).toAddSubgroup lambda :=
  cofinal_diagonal_rank A (j A) r lambda hlambda hr (insertion A) (recover A)
    (insertion_j A) (fun i q => recover_j A q i) (recover_insertion A) hα

end NoUniversalFSigma.Proof.Packet
