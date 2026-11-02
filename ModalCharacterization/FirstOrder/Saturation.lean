/-
Modal Characterization in Lean 4. Released under Apache-2.0; see LICENSE.
Uses mathlib's complete types and parameter structures (Aaron Anderson).
The mathematical source is Blackburn, de Rijke, Venema, Modal Logic,
2010 fourth corrected printing, Def. 2.63 and Thm. 2.65, pp. 101–102.
-/
module

public import ModalCharacterization.FirstOrder.PartialTypes

@[expose] public section

namespace ModalCharacterization.FirstOrder

open _root_.FirstOrder _root_.FirstOrder.Language

universe u v w
variable {L : _root_.FirstOrder.Language.{u, v}} {M : Type w}
variable [L.Structure M] [Nonempty M]

/-- Complete-one-type formulation of Blue Book Def. 2.63 for omega-saturation
(2010 printing, p. 101). For every finite parameter subset `A` of the specified
structure, every complete one-type over its full parameter theory is realized
in that same structure. Parameter constants denote their original elements.
The formula set and language have no cardinality bound. -/
def IsOmegaSaturated (L : _root_.FirstOrder.Language.{u, v}) (M : Type w)
    [L.Structure M] [Nonempty M] : Prop :=
  ∀ A : Set M, A.Finite →
    ∀ p : (L[[A]].completeTheory M).CompleteType (Fin 1),
      p ∈ (L[[A]].completeTheory M).realizedTypes M (Fin 1)

/-- Auxiliary realization step for Def. 2.63 / Thm. 2.65 (2010, pp. 101–102).
A partial one-type included in a complete type over a finite parameter set is
realized in the fixed omega-saturated structure, using mathlib's `realizedTypes`.
This does not construct a saturated structure or an extension. -/
theorem IsOmegaSaturated.realize_of_completeType
    (hM : IsOmegaSaturated L M) {A : Set M} (hA : A.Finite)
    {Γ : Set (L[[A]].Formula (Fin 1))}
    (p : (L[[A]].completeTheory M).CompleteType (Fin 1))
    (hp : Formula.equivSentence '' Γ ⊆ (p : L[[A]][[Fin 1]].Theory)) :
    ∃ v : Fin 1 → M, ∀ φ ∈ Γ, φ.Realize v := by
  obtain ⟨v, hv⟩ := hM A hA p
  refine ⟨v, fun φ hφ => ?_⟩
  apply (Theory.CompleteType.formula_mem_typeOf (T := L[[A]].completeTheory M)).mp
  rw [hv]
  exact hp ⟨φ, hφ, rfl⟩

/-- Partial-type realization bridge for Blue Book Thm. 2.65 (2010, p. 102).
Compactness and completion supply a complete type, then omega-saturation realizes
it in the original structure with the original finite parameter interpretation. -/
theorem IsOmegaSaturated.realize_finitelyRealized
    (hM : IsOmegaSaturated L M) {A : Set M} (hA : A.Finite)
    {Γ : Set (L[[A]].Formula (Fin 1))} (hΓ : FinitelyRealized M Γ) :
    ∃ v : Fin 1 → M, ∀ φ ∈ Γ, φ.Realize v := by
  obtain ⟨p, hp⟩ := exists_completeType_of_finitelyRealized M hΓ
  exact hM.realize_of_completeType hA p hp

/-- Representation equivalence for Blue Book Def. 2.63 (2010, p. 101):
the complete-one-type formulation is equivalent to realizing all finitely
realized partial one-types over finite parameter sets. The consistency
formulation in the book is connected by `finitelyRealized_iff_isSatisfiable`. -/
theorem isOmegaSaturated_iff_realizes_finitelyRealized :
    IsOmegaSaturated L M ↔
      ∀ A : Set M, A.Finite → ∀ Γ : Set (L[[A]].Formula (Fin 1)),
        FinitelyRealized M Γ → ∃ v : Fin 1 → M, ∀ φ ∈ Γ, φ.Realize v := by
  classical
  constructor
  · intro h A hA Γ hΓ
    exact h.realize_finitelyRealized hA hΓ
  · intro h A hA p
    let T := L[[A]].completeTheory M
    let Γ : Set (L[[A]].Formula (Fin 1)) :=
      Formula.equivSentence ⁻¹' (p : L[[A]][[Fin 1]].Theory)
    have hΓ : FinitelyRealized M Γ := by
      apply (finitelyRealized_iff_isSatisfiable M).mpr
      apply p.isMaximal.1.mono
      refine Set.union_subset p.subset ?_
      rintro ψ ⟨φ, hφ, rfl⟩
      exact hφ
    obtain ⟨v, hv⟩ := h A hA Γ hΓ
    have hp : ∀ ψ ∈ p, ψ ∈ T.typeOf v := by
      intro ψ hψ
      have hr := hv (Formula.equivSentence.symm ψ) (by simpa [Γ] using hψ)
      exact (Theory.CompleteType.mem_typeOf).mpr hr
    refine ⟨v, SetLike.ext fun ψ => ?_⟩
    constructor
    · intro hψ
      by_contra hn
      exact ((T.typeOf v).not_mem_iff ψ).mp (hp ψ.not ((p.not_mem_iff ψ).mpr hn)) hψ
    · exact hp ψ

/-- Explicit correspondence with the consistency formulation of Blue Book
Def. 2.63 for omega-saturation (2010 printing, p. 101). Consistency is
satisfiability of the complete parameter theory together with the partial type,
whose free variable is encoded as a fresh constant by mathlib. -/
theorem isOmegaSaturated_iff_realizes_consistent :
    IsOmegaSaturated L M ↔
      ∀ A : Set M, A.Finite → ∀ Γ : Set (L[[A]].Formula (Fin 1)),
        (((L[[A]]).lhomWithConstants (Fin 1)).onTheory (L[[A]].completeTheory M) ∪
          Formula.equivSentence '' Γ).IsSatisfiable →
            ∃ v : Fin 1 → M, ∀ φ ∈ Γ, φ.Realize v := by
  rw [isOmegaSaturated_iff_realizes_finitelyRealized]
  simp_rw [finitelyRealized_iff_isSatisfiable]

end ModalCharacterization.FirstOrder
