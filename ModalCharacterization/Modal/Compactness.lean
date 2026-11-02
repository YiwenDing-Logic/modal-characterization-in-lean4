/-
Modal Characterization in Lean. Released under Apache-2.0; see LICENSE.
Reuses Aaron Anderson's mathlib compactness theorem and CSLib finite conjunctions.
-/
module

public import ModalCharacterization.Modal.Characterization
public import ModalCharacterization.Modal.Saturation
public import Mathlib.ModelTheory.Satisfiability

@[expose] public section

namespace ModalCharacterization

open _root_.FirstOrder _root_.FirstOrder.Language Cslib.Logic.Modal

universe u v w
variable {Atom : Type u}

/-- Semantic conjunction helper for the first compactness step of Blue Book
Thm. 2.68 (2010 fourth corrected printing, p. 103), basic unimodal scope.
The standard translation of the finite modal conjunction has exactly the joint
truth conditions of the translated conjuncts, including the empty conjunction.
This asserts semantic correspondence, not syntactic equality of encodings. -/
theorem standardTranslation_finiteAnd_realize
    {W : Type v} [Nonempty W] (S : (language Atom).Structure W)
    (Φ : Finset (Unimodal.Proposition Atom)) (x : W) :
    letI := S
    (standardTranslation (Cslib.Logic.finiteAnd Φ.toList)).Realize (fun _ => x) ↔
      ∀ φ ∈ Φ, (standardTranslation φ).Realize (fun _ => x) := by
  let := S
  have hr (φ : Unimodal.Proposition Atom) :
      Satisfies (fromStructure S) x φ ↔
        (standardTranslation φ).Realize (fun _ => x) := by
    rw [standardTranslation_correct]
    unfold holds
    rw [toStructure_fromStructure]
  constructor
  · intro h φ hφ
    exact (hr φ).mp (Satisfies.finiteAnd_iff_forall.mp ((hr _).mpr h)
      φ (Finset.mem_toList.mpr hφ))
  · intro h
    exact (hr _).mp (Satisfies.finiteAnd_iff_forall.mpr
      fun φ hφ => (hr φ).mpr (h φ (Finset.mem_toList.mp hφ)))

/-- First compactness step in Blue Book Thm. 2.68 (2010 fourth corrected printing,
p. 103), basic unimodal scope: if `α` entails each translated member of `Γ` and
all those translations together entail `α`, a single finite modal conjunction
expresses `α`. The free variable is named by the SAME fresh constant throughout.
Entailment uses mathlib's theory semantics; its realization interface applies to
arbitrary model universes. No bisimulation, saturation or countability premise
is used. This proves the book's conditional claim, not the full characterization. -/
theorem modallyExpressible_of_modal_consequences_entail
    (α : (language Atom).Formula (Fin 1)) (Γ : Set (Unimodal.Proposition Atom))
    (hforward : ∀ φ ∈ Γ,
      ({Formula.equivSentence α} : (language Atom)[[Fin 1]].Theory) ⊨ᵇ
        Formula.equivSentence (standardTranslation φ))
    (hback : (fun φ => Formula.equivSentence (standardTranslation φ)) '' Γ ⊨ᵇ
      Formula.equivSentence α) : ModallyExpressible.{u, v} α := by
  classical
  obtain ⟨Δ, hΔ, hent⟩ := Theory.models_iff_finset_models.mp hback
  obtain ⟨Φ, hΦ, heq⟩ := Finset.subset_set_image_iff.mp hΔ
  refine ⟨Cslib.Logic.finiteAnd Φ.toList, ?_⟩
  intro W _ S x
  let := S
  let := constantsOn.structure (fun _ : Fin 1 => x)
  have hc (β : (language Atom).Formula (Fin 1)) :
      (Formula.equivSentence β).Realize W ↔ β.Realize (fun _ => x) :=
    Formula.realize_equivSentence W β
  rw [standardTranslation_finiteAnd_realize S Φ x]
  constructor
  · intro ha φ hφ
    have : W ⊨ ({Formula.equivSentence α} : (language Atom)[[Fin 1]].Theory) := by
      constructor
      intro ψ hψ
      have he : ψ = Formula.equivSentence α := Set.mem_singleton_iff.mp hψ
      subst ψ
      exact (hc α).mpr ha
    exact (hc _).mp ((hforward φ (hΦ hφ)).realize_sentence W)
  · intro hs
    have : W ⊨ (↑Δ : (language Atom)[[Fin 1]].Theory) := by
      constructor
      intro ψ hψ
      have hm : ψ ∈ Φ.image (fun φ => Formula.equivSentence (standardTranslation φ)) := by
        rw [heq]
        exact hψ
      obtain ⟨φ, hφ, rfl⟩ := Finset.mem_image.mp hm
      exact (hc _).mpr (hs φ hφ)
    exact (hc α).mp (hent.realize_sentence W)

/-- Representation helper for the pointed-model construction in Blue Book
Thm. 2.68 (2010 fourth corrected printing, p. 104). A sentence obtained by naming
the free variable of a standard translation is true exactly when its modal
formula is true at that named point in the reduct. The expansion hypothesis
ensures the original symbols keep their interpretations. -/
theorem standardTranslation_equivSentence_realize
    {W : Type v} [Nonempty W] [(language Atom).Structure W]
    [(language Atom)[[Fin 1]].Structure W]
    [((language Atom).lhomWithConstants (Fin 1)).IsExpansionOn W]
    (φ : Unimodal.Proposition Atom) :
    (Formula.equivSentence (standardTranslation φ)).Realize W ↔
      Satisfies (fromStructure (inferInstance : (language Atom).Structure W))
        ((language Atom).con (0 : Fin 1) : W) φ := by
  rw [Formula.realize_equivSentence]
  have hv : (fun a : Fin 1 => ((language Atom).con a : W)) =
      (fun _ => ((language Atom).con (0 : Fin 1) : W)) :=
    funext fun a => congrArg (fun i => ((language Atom).con i : W)) (Subsingleton.elim a 0)
  rw [hv, standardTranslation_correct]
  unfold holds
  rw [toStructure_fromStructure]

/-- Consistency claim in Blue Book Thm. 2.68 (2010 fourth corrected printing,
p. 104), basic unimodal scope. If a point satisfies every modal consequence of
`α`, its full translated modal theory together with `α` has a model with one
common named point. Uses compactness and the negation of a finite conjunction;
neither Detour, saturation nor bisimulation invariance is assumed here. -/
theorem isSatisfiable_modalTheory_insert_of_modal_consequences
    (α : (language Atom).Formula (Fin 1))
    {W : Type v} [Nonempty W] (M : Unimodal.Model W Atom) (x : W)
    (hM : ∀ φ : Unimodal.Proposition Atom,
      (({Formula.equivSentence α} : (language Atom)[[Fin 1]].Theory) ⊨ᵇ
        Formula.equivSentence (standardTranslation φ)) → Satisfies M x φ) :
    (insert (Formula.equivSentence α)
      ((fun φ => Formula.equivSentence (standardTranslation φ)) '' theory M x) :
      (language Atom)[[Fin 1]].Theory).IsSatisfiable := by
  classical
  let f := fun φ => Formula.equivSentence (standardTranslation (Atom := Atom) φ)
  apply Theory.isSatisfiable_iff_isFinitelySatisfiable.mpr
  intro Δ hΔ
  have hsub : (↑(Δ.erase (Formula.equivSentence α)) : Set _) ⊆ f '' theory M x := by
    intro ψ hψ
    have hm := Finset.mem_erase.mp hψ
    exact (hΔ hm.2).resolve_left hm.1
  obtain ⟨Φ, hΦ, heq⟩ := Finset.subset_set_image_iff.mp hsub
  have hfin : (insert (Formula.equivSentence α) (f '' (↑Φ : Set _)) :
      (language Atom)[[Fin 1]].Theory).IsSatisfiable := by
    by_contra hn
    let θ := Cslib.Logic.finiteAnd Φ.toList
    have hcon : ({Formula.equivSentence α} : (language Atom)[[Fin 1]].Theory) ⊨ᵇ
        f (.not θ) := by
      apply Theory.models_sentence_iff.mpr
      intro K
      let : (language Atom).Structure K :=
        ((language Atom).lhomWithConstants (Fin 1)).reduct K
      apply (standardTranslation_equivSentence_realize (.not θ)).mpr
      change ¬ Satisfies (fromStructure (inferInstance : (language Atom).Structure K))
        ((language Atom).con (0 : Fin 1) : K) θ
      intro hθ
      have : K ⊨ insert (Formula.equivSentence α) (f '' (↑Φ : Set _)) := by
        constructor
        intro ψ hψ
        rcases hψ with he | ⟨φ, hφ, he⟩
        · subst ψ
          exact K.is_model.realize_of_mem _ (Set.mem_singleton _)
        · subst ψ
          exact (standardTranslation_equivSentence_realize φ).mpr
            (Satisfies.finiteAnd_iff_forall.mp hθ φ (Finset.mem_toList.mpr hφ))
      exact hn (Theory.Model.isSatisfiable K)
    have hnot : Satisfies M x (.not θ) := hM (.not θ) hcon
    apply hnot
    exact Satisfies.finiteAnd_iff_forall.mpr
      fun φ hφ => hΦ (Finset.mem_toList.mp hφ)
  apply hfin.mono
  intro ψ hψ
  by_cases he : ψ = Formula.equivSentence α
  · exact Or.inl he
  · apply Or.inr
    have hm : ψ ∈ Φ.image f := by
      rw [heq]
      exact Finset.mem_erase.mpr ⟨he, hψ⟩
    obtain ⟨φ, hφ, rfl⟩ := Finset.mem_image.mp hm
    exact ⟨φ, hφ, rfl⟩

/-- Pointed-model construction in Blue Book Thm. 2.68 (2010 fourth corrected
printing, p. 104), basic unimodal scope: a point satisfying all modal consequences
of `α` is modally equivalent to a point satisfying `α`. Mathlib's satisfiable-model
witness is transported using `Theory.ModelType.ulift` to `Type (max u w)`;
the input carrier has independent universe `v`. This is an implementation helper
for universe alignment, not an additional book proposition. For `Atom : Type`,
choosing `w = v` puts the witness in the input world universe.
No countability of atoms or worlds, saturation or invariance is required. -/
theorem exists_modallyEquivalent_model_of_modal_consequences_ulift
    (α : (language Atom).Formula (Fin 1))
    {W : Type v} [Nonempty W] (M : Unimodal.Model W Atom) (x : W)
    (hM : ∀ φ : Unimodal.Proposition Atom,
      (({Formula.equivSentence α} : (language Atom)[[Fin 1]].Theory) ⊨ᵇ
        Formula.equivSentence (standardTranslation φ)) → Satisfies M x φ) :
    ∃ (W' : Type (max u w)) (hW' : Nonempty W'), letI := hW'
      ∃ (N : Unimodal.Model W' Atom) (y : W'),
        holds N α y ∧ ModallyEquivalent M N x y := by
  let hs := isSatisfiable_modalTheory_insert_of_modal_consequences α M x hM
  let K : Theory.ModelType.{0, u, max u w} _ := hs.some.ulift
  let : (language Atom).Structure K :=
    ((language Atom).lhomWithConstants (Fin 1)).reduct K
  let N := fromStructure (inferInstance : (language Atom).Structure K)
  let y : K := (language Atom).con (0 : Fin 1)
  refine ⟨K, inferInstance, N, y, ?_, ?_⟩
  · have ha := K.is_model.realize_of_mem (Formula.equivSentence α) (Set.mem_insert _ _)
    have hv : (fun a : Fin 1 => ((language Atom).con a : K)) = (fun _ => y) :=
      funext fun a => congrArg (fun i => ((language Atom).con i : K)) (Subsingleton.elim a 0)
    have hr := (Formula.realize_equivSentence K α).mp ha
    rw [hv] at hr
    unfold holds N
    rw [toStructure_fromStructure]
    exact hr
  · apply modallyEquivalent_of_theory_subset
    intro φ hφ
    apply (standardTranslation_equivSentence_realize φ).mp
    exact K.is_model.realize_of_mem _ (Set.mem_insert_of_mem _ ⟨φ, hφ, rfl⟩)

/-- Canonical-universe version of the pointed-model construction in Blue Book
Thm. 2.68 (2010 fourth corrected printing, p. 104), basic unimodal scope.
The witness is in the atom universe `u`; the input world universe is independent.
No saturation, invariance or countability premise is used. -/
theorem exists_modallyEquivalent_model_of_modal_consequences
    (α : (language Atom).Formula (Fin 1))
    {W : Type v} [Nonempty W] (M : Unimodal.Model W Atom) (x : W)
    (hM : ∀ φ : Unimodal.Proposition Atom,
      (({Formula.equivSentence α} : (language Atom)[[Fin 1]].Theory) ⊨ᵇ
        Formula.equivSentence (standardTranslation φ)) → Satisfies M x φ) :
    ∃ (W' : Type u) (hW' : Nonempty W'), letI := hW'
      ∃ (N : Unimodal.Model W' Atom) (y : W'),
        holds N α y ∧ ModallyEquivalent M N x y := by
  exact exists_modallyEquivalent_model_of_modal_consequences_ulift α M x hM

/-- Same-world-universe specialization of the pointed-model step of Blue Book
Thm. 2.68 (2010 fourth corrected printing, p. 104), for basic unimodal logic
with a small atom type. The world carrier remains arbitrary in `Type v`;
no countability of atoms or worlds is needed for this compactness step.
This helper aligns the witness with the existing same-universe invariance API. -/
theorem exists_modallyEquivalent_model_sameUniverse_of_modal_consequences
    {Atom : Type} (α : (language Atom).Formula (Fin 1))
    {W : Type v} [Nonempty W] (M : Unimodal.Model W Atom) (x : W)
    (hM : ∀ φ : Unimodal.Proposition Atom,
      (({Formula.equivSentence α} : (language Atom)[[Fin 1]].Theory) ⊨ᵇ
        Formula.equivSentence (standardTranslation φ)) → Satisfies M x φ) :
    ∃ (W' : Type v) (hW' : Nonempty W'), letI := hW'
      ∃ (N : Unimodal.Model W' Atom) (y : W'),
        holds N α y ∧ ModallyEquivalent M N x y := by
  exact exists_modallyEquivalent_model_of_modal_consequences_ulift α M x hM

/-- Auxiliary named-point translation for the compactness step of Blue Book
Thm. 2.76 (2010 fourth corrected printing, p. 109). A point realizing a modal
theory gives a model of its translations with one common named constant. -/
theorem isSatisfiable_translatedTheory_of_point
    (Γ : Set (Unimodal.Proposition Atom)) {W : Type v}
    (M : Unimodal.Model W Atom) (x : W) (h : ∀ φ ∈ Γ, Satisfies M x φ) :
    Theory.IsSatisfiable ((fun φ => Formula.equivSentence (standardTranslation φ)) '' Γ :
      (language Atom)[[Fin 1]].Theory) := by
  let : Nonempty W := ⟨x⟩
  let := toStructure M
  let := constantsOn.structure (fun _ : Fin 1 => x)
  have : W ⊨ ((fun φ => Formula.equivSentence (standardTranslation φ)) '' Γ :
      (language Atom)[[Fin 1]].Theory) := by
    constructor
    rintro ψ ⟨φ, hφ, rfl⟩
    exact (Formula.realize_equivSentence W (standardTranslation φ)).mpr
      ((standardTranslation_correct M φ x).mp (h φ hφ))
  exact Theory.Model.isSatisfiable W

/-- Modal compactness in the inconsistency form used by Blue Book Thm. 2.76
(2010 fourth corrected printing, p. 109), via mathlib first-order compactness
and the standard translation. Atoms lie in `Type`; worlds range over all
carriers in arbitrary `Type v`. Includes the empty finite subset. -/
theorem exists_finite_unsatisfiable_of_unsatisfiable
    {Atom : Type} (Γ : Set (Unimodal.Proposition Atom))
    (h : ¬ ∃ (W : Type v) (M : Unimodal.Model W Atom) (x : W),
      ∀ φ ∈ Γ, Satisfies M x φ) :
    ∃ Δ : Finset (Unimodal.Proposition Atom), (∀ φ ∈ Δ, φ ∈ Γ) ∧
      ¬ ∃ (W : Type v) (M : Unimodal.Model W Atom) (x : W),
        ∀ φ ∈ Δ, Satisfies M x φ := by
  classical
  let f := fun φ => Formula.equivSentence (standardTranslation (Atom := Atom) φ)
  have hn : ¬ Theory.IsSatisfiable (f '' Γ : (language Atom)[[Fin 1]].Theory) := by
    intro hs
    let K : Theory.ModelType.{0, 0, v} _ := hs.some.ulift
    let : (language Atom).Structure K := ((language Atom).lhomWithConstants (Fin 1)).reduct K
    apply h
    refine ⟨K, fromStructure (inferInstance : (language Atom).Structure K),
      (language Atom).con (0 : Fin 1), ?_⟩
    intro φ hφ
    exact (standardTranslation_equivSentence_realize φ).mp
      (K.is_model.realize_of_mem _ ⟨φ, hφ, rfl⟩)
  rw [Theory.isSatisfiable_iff_isFinitelySatisfiable, Theory.IsFinitelySatisfiable] at hn
  push Not at hn
  obtain ⟨Δ, hΔ, hnΔ⟩ := hn
  obtain ⟨Φ, hΦ, heq⟩ := Finset.subset_set_image_iff.mp hΔ
  refine ⟨Φ, hΦ, ?_⟩
  rintro ⟨W, M, x, hx⟩
  apply hnΔ
  have hs := isSatisfiable_translatedTheory_of_point (↑Φ) M x hx
  apply hs.mono
  intro ψ hψ
  have : ψ ∈ Φ.image f := by rw [heq]; exact hψ
  obtain ⟨φ, hφ, rfl⟩ := Finset.mem_image.mp this
  exact ⟨φ, hφ, rfl⟩

end ModalCharacterization
