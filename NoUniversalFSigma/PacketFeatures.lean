module

public import NoUniversalFSigma.PacketFactorization
public import NoUniversalFSigma.FiniteTensorPi
public import NoUniversalFSigma.Features

@[expose] public section

/-! Finite packet spans and finitely supported product features. -/

noncomputable section

namespace NoUniversalFSigma.Proof

open Set Topology NoUniversalFSigma
open scoped lp

attribute [local instance] Classical.propDecidable

/-- The finite-coordinate product of finitely supported coefficient families. -/
def finsuppPi (S : Type) [Fintype S] (D : S → Type) (a : ∀ s, D s →₀ ℝ) :
    (∀ s, D s) →₀ ℝ := by
  classical
  exact Finsupp.onFinset (Fintype.piFinset fun s => (a s).support)
    (fun c => ∏ s, a s (c s)) (fun c hc => Fintype.mem_piFinset.mpr fun s =>
      Finsupp.mem_support_iff.mpr (Finset.prod_ne_zero_iff.mp hc s (Finset.mem_univ s)))

@[simp]
theorem finsuppPi_apply (S : Type) [Fintype S] (D : S → Type)
    (a : ∀ s, D s →₀ ℝ) (c : ∀ s, D s) : finsuppPi S D a c = ∏ s, a s (c s) := by
  classical
  exact Finsupp.onFinset_apply

theorem support_finsuppPi (S : Type) [Fintype S] (D : S → Type)
    (a : ∀ s, D s →₀ ℝ) :
    (finsuppPi S D a).support = Fintype.piFinset fun s => (a s).support := by
  classical
  ext c
  simp only [Finsupp.mem_support_iff, finsuppPi_apply, Finset.prod_ne_zero_iff,
    Fintype.mem_piFinset, Finset.mem_univ, forall_const]

/-- A product feature evaluates on elementary tensors as a product of scalar evaluations. -/
theorem hilbertFinsuppFunctional_finsuppPi (S : Type) [Fintype S] (D : S → Type)
    (a : ∀ s, D s →₀ ℝ) (x : ∀ s, ℓ²(D s, ℝ)) :
    hilbertFinsuppFunctional (finsuppPi S D a) (hilbertPi S D x) =
      ∏ s, hilbertFinsuppFunctional (a s) (x s) := by
  classical
  simp only [hilbertFinsuppFunctional_apply, support_finsuppPi, finsuppPi_apply,
    hilbertPi_apply, ← Finset.prod_mul_distrib]
  exact (Finset.prod_univ_sum (fun s => (a s).support) (fun s i => a s i * x s i)).symm

/-- Extend a feature to optional coordinates, undoing the packet's nonzero vector scaling. -/
def optionFeature {I : Type} (β : ℝ) (a : I →₀ ℝ) : Option I →₀ ℝ :=
  β⁻¹ • a.embDomain Function.Embedding.some

theorem optionFeature_apply_graph {I : Type} {β : ℝ} (hβ : β ≠ 0)
    (mass a : I →₀ ℝ) (v : ℓ²(I, ℝ)) :
    hilbertFinsuppFunctional (optionFeature β a) (hilbertOptionGraph mass β v) =
      hilbertFinsuppFunctional a v := by
  classical
  rw [optionFeature, hilbertFinsuppFunctional_smul]
  have h : hilbertFinsuppFunctional (a.embDomain Function.Embedding.some)
      (hilbertOptionGraph mass β v) = β * hilbertFinsuppFunctional a v := by
    simp only [hilbertFinsuppFunctional_apply, Finsupp.support_embDomain, Finset.sum_map,
      Function.Embedding.some_apply, Finsupp.embDomain_some_some, hilbertOptionGraph_some]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [h, ← mul_assoc, inv_mul_cancel₀ hβ, one_mul]

namespace Packet

variable (A : ℕ → AdmissibleFamily)

/-- The finite packet's algebraic span is `Fσ`. -/
theorem isSigma02_span_finitePacket (B : Finset ℕ) :
    IsSigma02 (Submodule.span ℝ (range (finitePacket A B)) : Set (HeadSpace A B)) := by
  apply isSigma02_span_hilbertPi B (fun n => Option (A n.val).Coord)
    (fun n => (A n.val).Param) (fun n => oneFactor A n.val)
  intro n
  exact isSigma02_span_hilbertOptionGraph (A n.val).mass (beta_ne_zero A n.val)
    (A n.val).j (A n.val).span_isSigma02

/-- The constant normalized feature uses the packet's distinguished mass coordinate. -/
def oneFactorFeature (n : ℕ) :
    (A n).NormalizedFeature → (Option (A n).Coord →₀ ℝ)
  | .inl _ => Finsupp.single none 1
  | a@(.inr _) => optionFeature (beta A n) ((A n).normalizedFunctional a)

theorem oneFactorFeature_apply (n : ℕ) (a : (A n).NormalizedFeature)
    (p : (A n).Param) :
    hilbertFinsuppFunctional (oneFactorFeature A n a) (oneFactor A n p) =
      hilbertFinsuppFunctional ((A n).normalizedFunctional a) ((A n).j p) := by
  classical
  cases a with
  | inl u => simp [oneFactorFeature, hilbertFinsuppFunctional_apply,
      AdmissibleFamily.normalizedFunctional, (A n).mass_one]
  | inr a => exact optionFeature_apply_graph (beta_ne_zero A n) _ _ _

/-- Countably many normalized finite-head feature choices. -/
abbrev HeadFeature (B : Finset ℕ) := ∀ n : B, (A n.val).NormalizedFeature

/-- A normalized finite-head feature is a genuine finitely supported ambient functional. -/
def headFunctional (B : Finset ℕ) (a : HeadFeature A B) : HeadCoord A B →₀ ℝ :=
  finsuppPi B (fun n => Option (A n.val).Coord) (fun n => oneFactorFeature A n.val (a n))

theorem headFunctional_apply (B : Finset ℕ) (a : HeadFeature A B) (p : HeadParam A B) :
    hilbertFinsuppFunctional (headFunctional A B a) (finitePacket A B p) =
      ∏ n : B, hilbertFinsuppFunctional ((A n.val).normalizedFunctional (a n))
        ((A n.val).j (p n)) := by
  rw [headFunctional, finitePacket, hilbertFinsuppFunctional_finsuppPi]
  exact Finset.prod_congr rfl fun n _ => oneFactorFeature_apply A n.val (a n) (p n)

instance headFeatureCountable (B : Finset ℕ) : Countable (HeadFeature A B) := by
  dsimp [HeadFeature]
  infer_instance

/-- Product feature values are locally constant on the finite parameter product. -/
theorem headFunctional_locallyConstant (B : Finset ℕ) (a : HeadFeature A B) :
    IsLocallyConstant (hilbertFinsuppFunctional (headFunctional A B a) ∘ finitePacket A B) := by
  let f (n : B) (p : HeadParam A B) :=
    hilbertFinsuppFunctional ((A n.val).normalizedFunctional (a n)) ((A n.val).j (p n))
  have hf (n : B) : IsLocallyConstant (f n) :=
    ((A n.val).normalizedFunctional_locallyConstant (a n)).comp_continuous (continuous_apply n)
  have hprod (T : Finset B) : IsLocallyConstant (fun p => ∏ n ∈ T, f n p) := by
    induction T using Finset.induction_on with
    | empty =>
      convert IsLocallyConstant.const (1 : ℝ) using 1
      funext p
      simp
    | @insert n T hn ih =>
      convert (hf n).mul ih using 1
      funext p
      simp only [Finset.prod_insert hn]
      rfl
  convert hprod Finset.univ using 1
  funext p
  exact headFunctional_apply A B a p

/-- The pinning conditions imposed by finite normalized features are clopen. -/
theorem isClopen_headFunctional_fiber (B : Finset ℕ) (a : HeadFeature A B) (r : ℝ) :
    IsClopen {p : HeadParam A B |
      hilbertFinsuppFunctional (headFunctional A B a) (finitePacket A B p) = r} :=
  (headFunctional_locallyConstant A B a).isClopen_fiber r

end Packet

end NoUniversalFSigma.Proof
