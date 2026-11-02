/- Modal Characterization in Lean. Released under Apache-2.0; see LICENSE. -/
module

public import ModalCharacterization

/-!
Small public semantic regressions. These are implementation checks, not further
numbered results of the Blue Book. They keep empty classes, empty formula sets,
independent valuations on one carrier, and empty successor sets visible.
-/

@[expose] public section

namespace ModalCharacterization.Verification

open Cslib.Logic.Modal

universe u v

/-- Boundary regression for the class convention of Blue Book Thm. 2.76
(2010 fourth corrected printing, p. 109): the empty pointed-model class is
defined by falsity, at every fixed world universe. This is a specialization,
not an additional book theorem. -/
theorem emptyClass_definableByFormula {Atom : Type} :
    PointedModelClass.IsDefinableByFormula
      (fun {W : Type v} (_ : Unimodal.Model W Atom) (_ : W) => False) := by
  refine ⟨.false, ?_⟩
  intro W M x
  rfl

/-- Boundary regression for theory definability in Blue Book Thm. 2.75
(2010 fourth corrected printing, pp. 107–109): the empty theory defines all
pointed models, with no nonemptiness requirement on the defining formula set. -/
theorem universalClass_emptyTheory {Atom : Type u} :
    PointedModelClass.IsModallyDefinable
      (fun {W : Type v} (_ : Unimodal.Model W Atom) (_ : W) => True) := by
  refine ⟨∅, ?_⟩
  intro W M x
  simp

/-- Boundary regression for single-formula definability in Blue Book Thm. 2.76
(2010 fourth corrected printing, p. 109): truth also defines the universal
pointed-model class. Together with `universalClass_emptyTheory`, this checks
the empty-conjunction boundary of the compactness conclusion. -/
theorem universalClass_definableByFormula {Atom : Type} :
    PointedModelClass.IsDefinableByFormula
      (fun {W : Type v} (_ : Unimodal.Model W Atom) (_ : W) => True) := by
  refine ⟨.not .false, ?_⟩
  intro W M x
  change True ↔ ¬ False
  simp

/-- Public regression fixture: a one-world basic unimodal model with no
successors and one atom whose valuation is the supplied proposition.
This is an implementation fixture, not a separately numbered book definition. -/
def oneWorldModel (value : Prop) : Unimodal.Model Unit Unit where
  toFrame := Cslib.Frame.ofRelation (fun _ _ => False)
  v := fun _ _ => value

/-- Regression for explicit model arguments in standard translation
(Blue Book Prop. 2.47(i), 2010 fourth corrected printing, p. 85) and atomic
bisimulation invariance (Thm. 2.20, p. 67). Two models on the same one-world
carrier with opposite valuations have different translated atomic truth and
cannot be bisimilar at that world. -/
theorem sameCarrier_valuation_separation :
    holds (oneWorldModel True) (standardTranslation (.atom ())) () ∧
      ¬ holds (oneWorldModel False) (standardTranslation (.atom ())) () ∧
      ¬ ModallyBisimilar (oneWorldModel True) (oneWorldModel False) () () := by
  constructor
  · exact (standardTranslation_correct _ (.atom ()) ()).mp trivial
  constructor
  · intro h
    exact (standardTranslation_correct _ (.atom ()) ()).mpr h
  · intro h
    exact (h.satisfies_iff (.atom ())).mp trivial

/-- Empty-successor regression for Blue Book Def. 2.53
(2010 fourth corrected printing, pp. 92–93): finite satisfiability requires
a witness even for the empty finite subset. Hence no formula set, including
the empty set, is finitely satisfiable among the successors of a dead end. -/
theorem noSuccessors_not_finitelySatisfiable
    {Atom : Type u} {W : Type v} (M : Unimodal.Model W Atom) (x : W)
    (hR : ∀ y, ¬ M.toFrame.rel x y) (Γ : Set (Unimodal.Proposition Atom)) :
    ¬ ModalFinitelySatisfiableIn M Γ {y | M.toFrame.rel x y} := by
  intro hΓ
  obtain ⟨y, hy, _⟩ := hΓ ∅ (by simp)
  exact hR y hy

/-- Empty-relation regression for Blue Book Def. 2.53
(2010 fourth corrected printing, pp. 92–93): every model with no accessibility
arrows is modally saturated, because finite satisfiability in each successor
set is impossible. This checks the boundary of the production definition. -/
theorem emptyRelation_isModallySaturated
    {Atom : Type u} {W : Type v} (M : Unimodal.Model W Atom)
    (hR : ∀ x y, ¬ M.toFrame.rel x y) : IsModallySaturated M := by
  intro x Γ hΓ
  exact False.elim (noSuccessors_not_finitelySatisfiable M x (hR x) Γ hΓ)

-- Check the regressions' own transitive dependencies as part of the build.
#check @emptyClass_definableByFormula
#print axioms emptyClass_definableByFormula
#check @universalClass_emptyTheory
#print axioms universalClass_emptyTheory
#check @universalClass_definableByFormula
#print axioms universalClass_definableByFormula
#check @sameCarrier_valuation_separation
#print axioms sameCarrier_valuation_separation
#check @noSuccessors_not_finitelySatisfiable
#print axioms noSuccessors_not_finitelySatisfiable
#check @emptyRelation_isModallySaturated
#print axioms emptyRelation_isModallySaturated

end ModalCharacterization.Verification
