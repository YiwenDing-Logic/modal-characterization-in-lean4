/-
Modal Characterization in Lean. Released under Apache-2.0; see LICENSE.
Follows Blackburn, de Rijke, Venema, Modal Logic (2010 fourth corrected printing),
Thm. 2.65, p. 102. Reuses mathlib parameter semantics and the project's CSLib adapter.
-/
module

public import ModalCharacterization.FirstOrder.Saturation
public import ModalCharacterization.Modal.StandardTranslation
public import ModalCharacterization.Modal.Saturation

@[expose] public section

namespace ModalCharacterization

open _root_.FirstOrder _root_.FirstOrder.Language Cslib.Logic.Modal

universe u v
variable {Atom : Type u} {W : Type v}

/-- The formula `R(c_a,x)` in the singleton-parameter language used in
Blue Book Thm. 2.65 (2010 printing, p. 102), basic unimodal specialization.
The parameter and the single free variable occupy distinct language layers. -/
def successorFormula (a : W) : (language Atom)[[({a} : Set W)]].Formula (Fin 1) :=
  (((language Atom).lhomWithConstants ({a} : Set W)).onRelation RelationSymbol.access).formula₂
    ((language Atom).con (⟨a, Set.mem_singleton a⟩ : ({a} : Set W))).term (.var 0)

/-- The partial type `{R(c_a,x)} ∪ ST_x(Γ)` from Blue Book Thm. 2.65
(2010 printing, p. 102). Standard translations are explicitly lifted into the
singleton-parameter language; no injectivity of the translation is assumed. -/
def successorType (a : W) (Γ : Set (Unimodal.Proposition Atom)) :
    Set ((language Atom)[[({a} : Set W)]].Formula (Fin 1)) :=
  insert (successorFormula a)
    ((fun φ => ((language Atom).lhomWithConstants ({a} : Set W)).onFormula
      (standardTranslation φ)) '' Γ)

/-- Parameter-semantics helper for the accessibility requirement of Thm. 2.65
(2010 printing, p. 102): the named constant denotes the original world `a`. -/
theorem successorFormula_realize (M : Unimodal.Model W Atom) [Nonempty W]
    (a : W) (v : Fin 1 → W) :
    letI : (language Atom).Structure W := toStructure M
    (successorFormula (Atom := Atom) a).Realize v ↔ M.toFrame.rel a (v 0) := by
  let : (language Atom).Structure W := toStructure M
  simp only [successorFormula, Formula.realize_rel₂, Term.realize_con, Term.realize_var]
  rfl

/-- Finite-realization step of Blue Book Thm. 2.65 (2010 printing, p. 102),
basic unimodal specialization. Finitely many translated constraints have finitely
many modal preimages, jointly realizable by a successor in the original model. -/
theorem successorType_finitelyRealized (M : Unimodal.Model W Atom) [Nonempty W]
    (a : W) {Γ : Set (Unimodal.Proposition Atom)}
    (hΓ : ModalFinitelySatisfiableIn M Γ {b | M.toFrame.rel a b}) :
    letI : (language Atom).Structure W := toStructure M
    FirstOrder.FinitelyRealized W (successorType a Γ) := by
  classical
  let : (language Atom).Structure W := toStructure M
  let f := fun φ => ((language Atom).lhomWithConstants ({a} : Set W)).onFormula
    (standardTranslation φ)
  intro Δ hΔ
  have hsub : (↑(Δ.erase (successorFormula a)) : Set _) ⊆ f '' Γ := by
    intro ψ hψ
    have hm := Finset.mem_erase.mp hψ
    exact (hΔ hm.2).resolve_left hm.1
  obtain ⟨Φ, hΦ, heq⟩ := Finset.subset_set_image_iff.mp hsub
  obtain ⟨b, hb, hs⟩ := hΓ Φ (fun φ hφ => hΦ hφ)
  refine ⟨fun _ => b, fun ψ hψ => ?_⟩
  by_cases hedge : ψ = successorFormula a
  · subst ψ
    exact (successorFormula_realize M a (fun _ => b)).mpr hb
  · have hm : ψ ∈ Φ.image f := by
      rw [heq]
      exact Finset.mem_erase.mpr ⟨hedge, hψ⟩
    obtain ⟨φ, hφ, rfl⟩ := Finset.mem_image.mp hm
    apply (LHom.realize_onFormula ((language Atom).lhomWithConstants ({a} : Set W))
      (standardTranslation φ)).mpr
    exact (standardTranslation_correct M φ b).mp (hs φ hφ)

/-- Blue Book Thm. 2.65 (2010 printing, p. 102), basic unimodal specialization
over nonempty models: first-order omega-saturation implies modal saturation.
The proof names one parameter, realizes `{R(c_a,x)} ∪ ST_x(Γ)` in the same model,
and recovers modal truth by Prop. 2.47(i). No countability of the world domain or
formula set is assumed; existence of omega-saturated structures is not asserted. -/
theorem isModallySaturated_of_isOmegaSaturated
    (M : Unimodal.Model W Atom) [Nonempty W]
    (hM : letI : (language Atom).Structure W := toStructure M
      FirstOrder.IsOmegaSaturated (language Atom) W) : IsModallySaturated M := by
  let : (language Atom).Structure W := toStructure M
  intro a Γ hΓ
  obtain ⟨v, hv⟩ := hM.realize_finitelyRealized (Set.finite_singleton a)
    (successorType_finitelyRealized M a hΓ)
  have hedge := hv (successorFormula a) (Set.mem_insert _ _)
  refine ⟨v 0, (successorFormula_realize M a v).mp hedge, fun φ hφ => ?_⟩
  have hφ' := hv (((language Atom).lhomWithConstants ({a} : Set W)).onFormula
    (standardTranslation φ)) (Set.mem_insert_of_mem _ ⟨φ, hφ, rfl⟩)
  have hst := (LHom.realize_onFormula ((language Atom).lhomWithConstants ({a} : Set W))
    (standardTranslation φ)).mp hφ'
  have heq : v = fun _ => v 0 := funext fun i => congrArg v (Subsingleton.elim i 0)
  rw [heq] at hst
  exact (standardTranslation_correct M φ (v 0)).mpr hst

/-- The Hennessy–Milner conclusion of Blue Book Thm. 2.65 (2010 printing, p. 102),
basic unimodal specialization, obtained through Prop. 2.54. The models can have
different world types; their first-order structures are supplied separately. -/
theorem modallyEquivalent_iff_bisimilar_of_isOmegaSaturated
    {W' : Type*} (M : Unimodal.Model W Atom) (N : Unimodal.Model W' Atom)
    [Nonempty W] [Nonempty W']
    (hM : letI : (language Atom).Structure W := toStructure M
      FirstOrder.IsOmegaSaturated (language Atom) W)
    (hN : letI : (language Atom).Structure W' := toStructure N
      FirstOrder.IsOmegaSaturated (language Atom) W') {x : W} {y : W'} :
    ModallyEquivalent M N x y ↔ ModallyBisimilar M N x y :=
  (isModallySaturated_of_isOmegaSaturated M hM).modallyEquivalent_iff_bisimilar
    (isModallySaturated_of_isOmegaSaturated N hN)

end ModalCharacterization
