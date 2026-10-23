module

public import NoUniversalFSigma.FinitePi
public import NoUniversalFSigma.FiniteTensor

@[expose] public section

/-! Finite dependent products of algebraic tensor spans preserve the `Fσ` property. -/

namespace NoUniversalFSigma.Proof

open Set NoUniversalFSigma
open scoped lp

/-- Transport a generated span along a coordinate isometry and a surjective parametrization. -/
theorem isSigma02_span_range_reindex {I J P Q : Type}
    (e : I ≃ J) (u : P → ℓ²(I, ℝ)) (v : Q → ℓ²(J, ℝ))
    (g : P → Q) (hg : Function.Surjective g)
    (heq : ∀ p, hilbertReindex e (u p) = v (g p))
    (hv : IsSigma02 (Submodule.span ℝ (range v) : Set ℓ²(J, ℝ))) :
    IsSigma02 (Submodule.span ℝ (range u) : Set ℓ²(I, ℝ)) := by
  let R := hilbertReindex e
  have hrange : R '' range u = range v := by
    ext y
    constructor
    · rintro ⟨_, ⟨p, rfl⟩, rfl⟩
      exact ⟨g p, (heq p).symm⟩
    · rintro ⟨q, rfl⟩
      obtain ⟨p, rfl⟩ := hg q
      exact ⟨u p, ⟨p, rfl⟩, heq p⟩
  have hmap : (Submodule.span ℝ (range u)).map R.toLinearMap =
      Submodule.span ℝ (range v) := by
    rw [Submodule.map_span]
    exact congrArg (Submodule.span ℝ) hrange
  have hset : (Submodule.span ℝ (range u) : Set ℓ²(I, ℝ)) =
      R ⁻¹' (Submodule.span ℝ (range v) : Set ℓ²(J, ℝ)) := by
    ext x
    change x ∈ Submodule.span ℝ (range u) ↔ R x ∈ Submodule.span ℝ (range v)
    rw [← hmap, Submodule.mem_map]
    constructor
    · exact fun hx => ⟨x, hx, rfl⟩
    · rintro ⟨y, hy, he⟩
      exact R.injective he ▸ hy
  rw [hset]
  exact BorelHierarchy.isSigma02_preimage R.continuous hv

private def FiniteTensorPiProperty (S : Type) [Fintype S] : Prop :=
  ∀ (D : S → Type) [∀ s, Countable (D s)] (P : S → Type)
    (u : ∀ s, P s → ℓ²(D s, ℝ)),
    (∀ s, IsSigma02 (Submodule.span ℝ (range (u s)) : Set ℓ²(D s, ℝ))) →
    IsSigma02 (Submodule.span ℝ
      (range fun p : ∀ s, P s => hilbertPi S D (fun s => u s (p s))) :
        Set ℓ²((∀ s, D s), ℝ))

private theorem finiteTensorPiProperty (S : Type) [Fintype S] : FiniteTensorPiProperty S := by
  classical
  refine Fintype.induction_empty_option (P := FiniteTensorPiProperty) ?_ ?_ ?_ S
  · intro A B _ e ih
    let : Fintype A := Fintype.ofEquiv B e.symm
    intro D _ P u hu
    have hA := ih (fun a => D (e a)) (fun a => P (e a))
      (fun a => u (e a)) (fun a => hu (e a))
    let ec : (∀ b : B, D b) ≃ (∀ a : A, D (e a)) := Equiv.piCongrLeft' D e.symm
    let ep : (∀ b : B, P b) ≃ (∀ a : A, P (e a)) := Equiv.piCongrLeft' P e.symm
    apply isSigma02_span_range_reindex ec _ _ ep ep.surjective _ hA
    intro p
    ext c
    change (∏ b, u b (p b) ((ec.symm c) b)) = ∏ a, u (e a) ((ep p) a) (c a)
    rw [← e.prod_comp (fun b => u b (p b) ((ec.symm c) b))]
    apply Finset.prod_congr rfl
    intro a _
    change u (e a) (p (e a)) ((ec.symm c) (e a)) = u (e a) (p (e a)) (c a)
    exact congrArg (fun d => u (e a) (p (e a)) d)
      (Equiv.piCongrLeft'_symm_apply_apply D e.symm c a)
  · intro D _ P u _hu
    let : Unique (∀ s : PEmpty, P s) :=
      ⟨⟨fun s => PEmpty.elim s⟩, fun x => funext fun s => PEmpty.elim s⟩
    let : FiniteDimensional ℝ (Submodule.span ℝ
        (range fun p : ∀ s, P s => hilbertPi PEmpty D (fun s => u s (p s)))) :=
      FiniteDimensional.span_of_finite ℝ (finite_range _)
    exact BorelHierarchy.isPi01_isSigma02 (Submodule.closed_of_finiteDimensional _)
  · intro A _ ih D _ P u hu
    have hA := ih (fun a => D (some a)) (fun a => P (some a))
      (fun a => u (some a)) (fun a => hu (some a))
    have hbinary := isSigma02_algebraicTensorSpan
      (Submodule.span ℝ (range (u none)))
      (Submodule.span ℝ (range fun p : ∀ a : A, P (some a) =>
        hilbertPi A (fun a => D (some a)) (fun a => u (some a) (p a))))
      (hu none) hA
    rw [algebraicTensorSpan_span_range] at hbinary
    let ec : (∀ s : Option A, D s) ≃ D none × (∀ a : A, D (some a)) :=
      Equiv.piOptionEquivProd
    let ep : (∀ s : Option A, P s) ≃ P none × (∀ a : A, P (some a)) :=
      Equiv.piOptionEquivProd
    apply isSigma02_span_range_reindex ec _ _ ep ep.surjective _ hbinary
    intro p
    ext c
    change (∏ s, u s (p s) ((ec.symm c) s)) =
      u none (ep p).1 c.1 * ∏ a, u (some a) ((ep p).2 a) (c.2 a)
    rw [Fintype.prod_option]
    rfl

/-- The algebraic span of a finite dependent product of generating families is `Fσ`
whenever the span of each family is `Fσ`. -/
theorem isSigma02_span_hilbertPi (S : Type) [Fintype S] (D : S → Type)
    [∀ s, Countable (D s)] (P : S → Type) (u : ∀ s, P s → ℓ²(D s, ℝ))
    (hu : ∀ s, IsSigma02 (Submodule.span ℝ (range (u s)) : Set ℓ²(D s, ℝ))) :
    IsSigma02 (Submodule.span ℝ
      (range fun p : ∀ s, P s => hilbertPi S D (fun s => u s (p s))) :
        Set ℓ²((∀ s, D s), ℝ)) :=
  finiteTensorPiProperty S D P u hu

/-- The algebraic tensor span of a finite dependent family of Hilbert subspaces. -/
noncomputable def algebraicPiSpan (S : Type) [Fintype S] (D : S → Type)
    (H : ∀ s, Submodule ℝ ℓ²(D s, ℝ)) : Submodule ℝ ℓ²((∀ s, D s), ℝ) :=
  Submodule.span ℝ (range fun p : ∀ s, H s => hilbertPi S D (fun s => p s))

/-- Finite dependent algebraic tensor products of `Fσ` subspaces are `Fσ`. -/
theorem isSigma02_algebraicPiSpan (S : Type) [Fintype S] (D : S → Type)
    [∀ s, Countable (D s)] (H : ∀ s, Submodule ℝ ℓ²(D s, ℝ))
    (hH : ∀ s, IsSigma02 (H s : Set ℓ²(D s, ℝ))) :
    IsSigma02 (algebraicPiSpan S D H : Set ℓ²((∀ s, D s), ℝ)) := by
  apply isSigma02_span_hilbertPi S D (fun s => H s) (fun _ p => p)
  intro s
  have hrange : range (fun p : H s => (p : ℓ²(D s, ℝ))) = (H s : Set ℓ²(D s, ℝ)) := by
    ext x
    simp
  rw [hrange, Submodule.span_eq]
  exact hH s

end NoUniversalFSigma.Proof
