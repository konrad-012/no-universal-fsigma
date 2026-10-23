module

public import Mathlib

@[expose] public section

/-! Closed-cover derivatives and their countable termination. -/

namespace NoUniversalFSigma.Proof

open Set Topology TopologicalSpace Ordinal OrdinalApprox
open scoped Ordinal

universe u

variable {X : Type u} [TopologicalSpace X]

/-- An antitone closed-set chain in a second-countable space stabilizes at a successor
before the first uncountable ordinal. -/
theorem exists_countable_successor_eq [SecondCountableTopology X]
    (A : Ordinal.{u} → Set X) (hclosed : ∀ a, IsClosed (A a)) (hanti : Antitone A) :
    ∃ a < ω₁, A (a + 1) = A a := by
  classical
  obtain ⟨S, hS, hcover⟩ := isOpen_iUnion_countable
    (fun a : Iio (ω₁ : Ordinal.{u}) => (A a.1)ᶜ) (fun a => (hclosed a.1).isOpen_compl)
  let : Countable S := hS.to_subtype
  let a : Ordinal.{u} := ⨆ i : S, i.1.1
  have ha : a < ω₁ := Ordinal.iSup_lt_omega_one fun i : S => i.1.2
  refine ⟨a, ha, subset_antisymm (hanti (lt_add_one a).le) ?_⟩
  intro x hx
  by_contra hnext
  have hmem : x ∈ ⋃ i : Iio (ω₁ : Ordinal.{u}), (A i.1)ᶜ :=
    mem_iUnion.mpr ⟨⟨a + 1, (Cardinal.isSuccLimit_omega 1).succ_lt ha⟩, hnext⟩
  rw [← hcover] at hmem
  obtain ⟨i, hiS, hxi⟩ := mem_iUnion₂.mp hmem
  exact hxi (hanti (Ordinal.le_iSup (fun i : S => i.1.1) ⟨i, hiS⟩) hx)

/-- Points at which every neighborhood meets `A` outside each member of the cover. -/
def coverDerivative (C : ℕ → Set X) (A : Set X) : Set X :=
  A ∩ ⋂ k, closure (A \ C k)

theorem coverDerivative_subset (C : ℕ → Set X) (A : Set X) :
    coverDerivative C A ⊆ A := inter_subset_left

theorem coverDerivative_mono (C : ℕ → Set X) : Monotone (coverDerivative C) := by
  intro A B hAB
  exact inter_subset_inter hAB (iInter_mono fun k => closure_mono (sdiff_subset_sdiff_left hAB))

theorem isClosed_coverDerivative (C : ℕ → Set X) {A : Set X} (hA : IsClosed A) :
    IsClosed (coverDerivative C A) := hA.inter (isClosed_iInter fun _ => isClosed_closure)

/-- Removal is exactly the existence of a relatively bounded neighborhood. -/
theorem not_mem_coverDerivative_iff (C : ℕ → Set X) {A : Set X} {x : X} (hx : x ∈ A) :
    x ∉ coverDerivative C A ↔
      ∃ k, ∃ U : Set X, IsOpen U ∧ x ∈ U ∧ A ∩ U ⊆ C k := by
  constructor
  · intro hnot
    have hn : ¬ ∀ k, x ∈ closure (A \ C k) :=
      fun h => hnot ⟨hx, mem_iInter.mpr h⟩
    obtain ⟨k, hk⟩ := not_forall.mp hn
    refine ⟨k, (closure (A \ C k))ᶜ, isClosed_closure.isOpen_compl, hk, ?_⟩
    intro y hy
    by_contra hyC
    exact hy.2 (subset_closure ⟨hy.1, hyC⟩)
  · rintro ⟨k, U, hU, hxU, hbound⟩ hD
    obtain ⟨y, hyU, hyA, hyC⟩ := mem_closure_iff.mp (mem_iInter.mp hD.2 k) U hU hxU
    exact hyC (hbound ⟨hyA, hyU⟩)

/-- The derivative as an order-preserving map, for transfinite iteration. -/
def coverDerivativeOrderHom (C : ℕ → Set X) : Set X →o Set X :=
  ⟨coverDerivative C, coverDerivative_mono C⟩

/-- Transfinite remainders of the closed-cover derivative. -/
def coverRemainder (C : ℕ → Set X) (A : Set X) : Ordinal.{u} → Set X :=
  gfpApprox (coverDerivativeOrderHom C) A

@[simp] theorem coverRemainder_zero (C : ℕ → Set X) (A : Set X) :
    coverRemainder C A 0 = A := gfpApprox_zero _

@[simp] theorem coverRemainder_add_one (C : ℕ → Set X) (A : Set X) (a : Ordinal.{u}) :
    coverRemainder C A (a + 1) = coverDerivative C (coverRemainder C A a) :=
  gfpApprox_add_one _ (coverDerivative_subset C A) a

theorem coverRemainder_limit (C : ℕ → Set X) (A : Set X) {a : Ordinal.{u}}
    (ha : Order.IsSuccLimit a) :
    coverRemainder C A a = ⋂ b : Iio a, coverRemainder C A b.1 :=
  gfpApprox_of_isSuccLimit _ ha

theorem coverRemainder_antitone (C : ℕ → Set X) (A : Set X) :
    Antitone (coverRemainder C A) := gfpApprox_anti_right _

theorem coverRemainder_subset (C : ℕ → Set X) (A : Set X) (a : Ordinal.{u}) :
    coverRemainder C A a ⊆ A := gfpApprox_le _

theorem isClosed_coverRemainder (C : ℕ → Set X) {A : Set X} (hA : IsClosed A)
    (a : Ordinal.{u}) : IsClosed (coverRemainder C A a) := by
  induction a using Ordinal.limitRecOn with
  | zero => simpa using hA
  | add_one a ih => simpa using isClosed_coverDerivative C ih
  | limit a ha ih =>
    rw [coverRemainder_limit C A ha]
    exact isClosed_iInter fun b => ih b.1 b.2

/-- A closed countable cover removes at least one point from every nonempty closed set. -/
theorem coverDerivative_ne_self [PolishSpace X] (C : ℕ → Set X)
    (hC : ∀ k, IsClosed (C k)) (hcover : ⋃ k, C k = Set.univ)
    {A : Set X} (hA : IsClosed A) (hne : A.Nonempty) : coverDerivative C A ≠ A := by
  let : PolishSpace A := hA.polishSpace
  let : Nonempty A := hne.to_subtype
  have hcoverA : ⋃ k, (Subtype.val ⁻¹' C k : Set A) = Set.univ := by
    ext x
    simp only [mem_iUnion, mem_preimage, mem_univ, iff_true]
    have hx : x.1 ∈ ⋃ k, C k := by rw [hcover]; trivial
    exact mem_iUnion.mp hx
  obtain ⟨k, x, hx⟩ := nonempty_interior_of_iUnion_of_closed
    (fun k => (hC k).preimage continuous_subtype_val) hcoverA
  obtain ⟨U, hU, hUeq⟩ := isOpen_induced_iff.mp
    (isOpen_interior : IsOpen (interior (Subtype.val ⁻¹' C k : Set A)))
  have hxU : x.1 ∈ U := by
    change x ∈ Subtype.val ⁻¹' U
    rw [hUeq]
    exact hx
  have hxnot : x.1 ∉ closure (A \ C k) := by
    intro hcl
    obtain ⟨y, hyU, hyA, hyC⟩ := mem_closure_iff.mp hcl U hU hxU
    have hy : (⟨y, hyA⟩ : A) ∈ interior (Subtype.val ⁻¹' C k : Set A) := by
      rw [← hUeq]
      exact hyU
    have hyCk : (⟨y, hyA⟩ : A) ∈ Subtype.val ⁻¹' C k := interior_subset hy
    exact hyC hyCk
  intro heq
  have hxD : x.1 ∈ coverDerivative C A := by rw [heq]; exact x.2
  exact hxnot (mem_iInter.mp hxD.2 k)

/-- Closed-cover derivatives in a Polish space vanish at a countable stage. -/
theorem exists_countable_coverRemainder_empty [PolishSpace X] (C : ℕ → Set X)
    (hC : ∀ k, IsClosed (C k)) (hcover : ⋃ k, C k = Set.univ)
    {A : Set X} (hA : IsClosed A) :
    ∃ a < ω₁, coverRemainder C A a = ∅ := by
  obtain ⟨a, ha, hfix⟩ := exists_countable_successor_eq (coverRemainder C A)
    (isClosed_coverRemainder C hA) (coverRemainder_antitone C A)
  refine ⟨a, ha, ?_⟩
  by_contra hne
  exact coverDerivative_ne_self C hC hcover (isClosed_coverRemainder C hA a)
    (nonempty_iff_ne_empty.mpr hne) (by simpa only [coverRemainder_add_one] using hfix)

end NoUniversalFSigma.Proof
