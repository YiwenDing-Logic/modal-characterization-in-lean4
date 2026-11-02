/-
Modal Characterization in Lean 4. Released under Apache-2.0; see LICENSE.
Auxiliary first-order infrastructure using mathlib's compactness and complete types.
The reused model-theory APIs are by Aaron Anderson (mathlib, Apache-2.0).
-/
module

public import Mathlib.ModelTheory.Types

@[expose] public section

namespace ModalCharacterization.FirstOrder

open _root_.FirstOrder _root_.FirstOrder.Language

universe u v w
variable {L : Language.{u, v}} (M : Type w) [L.Structure M]

/-- Auxiliary interface for Blue Book Def. 2.63 (2010 printing, p. 101) and
Thm. 2.65 (p. 102): each finite subset of a one-variable formula set has a
simultaneous realization in the given structure. The empty subset is included. -/
def FinitelyRealized (Γ : Set (L.Formula (Fin 1))) : Prop :=
  ∀ Δ : Finset (L.Formula (Fin 1)), (↑Δ : Set _) ⊆ Γ →
    ∃ v : Fin 1 → M, ∀ φ ∈ Δ, φ.Realize v

variable [Nonempty M] {Γ : Set (L.Formula (Fin 1))}

/-- Auxiliary consistency bridge for Blue Book Def. 2.63 and Thm. 2.65
(2010 printing, pp. 101–102). Compactness converts finite realization in `M`
into consistency with its complete theory; conversely existential closure
transfers each finite conjunction back to `M`. No language cardinality bound
or restriction on the size of the formula set is imposed. -/
theorem finitelyRealized_iff_isSatisfiable :
    FinitelyRealized M Γ ↔
      ((L.lhomWithConstants (Fin 1)).onTheory (L.completeTheory M) ∪
        Formula.equivSentence '' Γ).IsSatisfiable := by
  classical
  constructor
  · intro h
    apply Theory.isSatisfiable_iff_isFinitelySatisfiable.mpr
    intro Δ hΔ
    let E := Δ.filter (· ∈ Formula.equivSentence '' Γ)
    let F := E.image Formula.equivSentence.symm
    have hF : (↑F : Set _) ⊆ Γ := by
      intro φ hφ
      obtain ⟨ψ, hψ, rfl⟩ := Finset.mem_image.mp hφ
      obtain ⟨χ, hχ, rfl⟩ := (Finset.mem_filter.mp hψ).2
      simpa using hχ
    obtain ⟨v, hv⟩ := h F hF
    let := constantsOn.structure v
    have : M ⊨ (L.lhomWithConstants (Fin 1)).onTheory (L.completeTheory M) :=
      (LHom.onTheory_model _ _).mpr inferInstance
    have : M ⊨ (↑Δ : L[[Fin 1]].Theory) := by
      constructor
      intro ψ hψ
      rcases hΔ hψ with hb | hg
      · exact Theory.realize_sentence_of_mem _ hb
      · apply (Formula.realize_equivSentence_symm M ψ v).mp
        exact hv _ (Finset.mem_image.mpr ⟨ψ, Finset.mem_filter.mpr ⟨hψ, hg⟩, rfl⟩)
    exact Theory.Model.isSatisfiable M
  · intro h Δ hΔ
    let N := h.some
    let := (L.lhomWithConstants (Fin 1)).reduct N
    have : N ⊨ (L.lhomWithConstants (Fin 1)).onTheory (L.completeTheory M) :=
      Theory.Model.mono N.is_model Set.subset_union_left
    have : N ⊨ L.completeTheory M :=
      (LHom.onTheory_model (L.lhomWithConstants (Fin 1)) (L.completeTheory M)).mp inferInstance
    let φ : L.Formula (Fin 1) := Formula.iInf (fun ψ : Δ => ψ.val)
    have hn : φ.Realize (fun a => (L.con a : N)) := by
      apply Formula.realize_iInf.mpr
      intro ψ
      apply (Formula.realize_equivSentence N _).mp
      exact N.is_model.realize_of_mem _ (Or.inr ⟨ψ.val, hΔ ψ.property, rfl⟩)
    have he : φ.exClosure.Realize N :=
      Formula.realize_exClosure_of_realize_equivSentence
        ((Formula.realize_equivSentence N _).mpr hn)
    have hm : φ.exClosure.Realize M := (realize_iff_of_model_completeTheory M N _).mp he
    obtain ⟨v, hv⟩ := (Formula.exists_realize_equivSentence_iff_realize_exClosure).mpr hm
    have hv' : φ.Realize v := by
      simpa using (Formula.realize_equivSentence_symm M (Formula.equivSentence φ) v).mpr hv
    exact ⟨v, fun ψ hψ => Formula.realize_iInf.mp hv' ⟨ψ, hψ⟩⟩

/-- Auxiliary complete-type extension for the partial-type realization step in
Blue Book Thm. 2.65 (2010 printing, p. 102), using the complete-type interface
for Def. 2.63 (p. 101). This is an implementation bridge, not a separately
numbered result in the book. -/
theorem exists_completeType_of_finitelyRealized (h : FinitelyRealized M Γ) :
    ∃ p : (L.completeTheory M).CompleteType (Fin 1),
      Formula.equivSentence '' Γ ⊆ (p : L[[Fin 1]].Theory) := by
  have hs := (finitelyRealized_iff_isSatisfiable M).mp h
  exact Set.nonempty_iff_ne_empty.mpr fun he =>
    (Theory.CompleteType.setOfPred_subset_eq_empty_iff _).mp he hs

end ModalCharacterization.FirstOrder
