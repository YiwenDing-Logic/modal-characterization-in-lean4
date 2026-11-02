/- Modal Characterization in Lean. Released under Apache-2.0; see LICENSE.
Uses mathlib model theory and CSLib modal semantics; no experimental imports. -/
module
public import ModalCharacterization.Modal.Detour
public import ModalCharacterization.Modal.Compactness

@[expose] public section
namespace ModalCharacterization
open _root_.FirstOrder _root_.FirstOrder.Language Cslib.Logic.Modal
universe u v w z

/-- Pointwise MOC-to-formula implication in Blue Book Thm. 2.68 (2010 fourth
corrected printing, p. 104), for a countable small atom type and arbitrary nonempty
world carriers. Compactness supplies N,y satisfying α and the full modal theory;
the Detour step transfers α back. Uses the now-proved Lemma 2.73.
No saturation or size bound on the input model is assumed. -/
theorem holds_of_modal_consequences
    {Atom : Type} [Countable Atom]
    (α : (language Atom).Formula (Fin 1)) (hinv : BisimulationInvariant.{0, v} α)
    {W : Type v} [Nonempty W] (M : Unimodal.Model W Atom) (x : W)
    (hM : ∀ φ : Unimodal.Proposition Atom,
      (({Formula.equivSentence α} : (language Atom)[[Fin 1]].Theory) ⊨ᵇ
        Formula.equivSentence (standardTranslation φ)) → Satisfies M x φ) :
    holds M α x := by
  obtain ⟨W', hW', N, y, ha, heq⟩ :=
    exists_modallyEquivalent_model_sameUniverse_of_modal_consequences α M x hM
  let := hW'
  exact (formula_iff_of_modallyEquivalent α hinv M N x y heq).mpr ha

/-- Blue Book Thm. 2.68 (2010 fourth corrected
printing, pp. 103–104), countable small atom type, basic unimodal logic, arbitrary
nonempty world carriers at universe v. The modal witness precedes all models.
The converse uses both book compactness steps and the elementary Detour; the easy
direction is bisimulation invariance of the standard translation. The
countable-language saturation input is the proved Lemma 2.73; no saturation
or modal equivalence transfer hypothesis is assumed. -/
theorem vanBenthem
    {Atom : Type} [Countable Atom] (α : (language Atom).Formula (Fin 1)) :
    BisimulationInvariant.{0, v} α ↔ ModallyExpressible.{0, v} α := by
  constructor
  · intro hinv
    let Γ : Set (Unimodal.Proposition Atom) := {φ |
      ({Formula.equivSentence α} : (language Atom)[[Fin 1]].Theory) ⊨ᵇ
        Formula.equivSentence (standardTranslation φ)}
    apply modallyExpressible_of_modal_consequences_entail α Γ (fun _ h => h)
    rw [Theory.models_iff_not_satisfiable]
    intro hs
    let K : Theory.ModelType.{0, 0, v} _ := hs.some.ulift
    let : (language Atom).Structure K :=
      ((language Atom).lhomWithConstants (Fin 1)).reduct K
    let N := fromStructure (inferInstance : (language Atom).Structure K)
    let y : K := (language Atom).con (0 : Fin 1)
    have ha : holds N α y := by
      apply holds_of_modal_consequences α hinv N y
      intro φ hφ
      apply (standardTranslation_equivSentence_realize φ).mp
      exact K.is_model.realize_of_mem _ (Or.inl ⟨φ, hφ, rfl⟩)
    have hn : K ⊨ (Formula.equivSentence α).not :=
      K.is_model.realize_of_mem _ (Or.inr (Set.mem_singleton _))
    apply hn
    change K ⊨ Formula.equivSentence α
    rw [Formula.realize_equivSentence]
    have hv : (fun a : Fin 1 => ((language Atom).con a : K)) = (fun _ => y) :=
      funext fun a => congrArg (fun i => ((language Atom).con i : K)) (Subsingleton.elim a 0)
    rw [hv]
    unfold holds N at ha
    rw [toStructure_fromStructure] at ha
    exact ha
  · exact ModallyExpressible.bisimulationInvariant

end ModalCharacterization
