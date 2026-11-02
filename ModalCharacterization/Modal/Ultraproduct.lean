/-
Modal Characterization in Lean 4. Released under Apache-2.0; see LICENSE.
Reuses Aaron Anderson's mathlib ultraproducts and the CSLib modal model interface.
-/
module

public import Mathlib.ModelTheory.Ultraproducts
public import ModalCharacterization.Modal.StandardTranslation

@[expose] public section

namespace ModalCharacterization

open _root_.FirstOrder _root_.FirstOrder.Language Cslib.Logic.Modal

universe u v z
variable {Atom : Type u} {I : Type z} {W : I → Type v}

/-- Blue Book Defs. 2.69–2.70 (2010 fourth corrected printing, p. 105),
specialized to nonempty basic unimodal models with possibly different carriers.
The carrier and first-order structure are mathlib's dependent-family ultraproduct.
The resulting world universe is `max z v`; indices need not be countable. -/
def modalUltraproduct (M : ∀ i, Unimodal.Model (W i) Atom)
    [∀ i, Nonempty (W i)] (U : Ultrafilter I) :
    Unimodal.Model ((U : Filter I).Product W) Atom :=
  letI : ∀ i, (language Atom).Structure (W i) := fun i => toStructure (M i)
  fromStructure (inferInstance : (language Atom).Structure ((U : Filter I).Product W))

/-- Valuation clause of Blue Book Def. 2.70(ii)
(2010 fourth corrected printing, p. 105), for basic unimodal ultraproducts. -/
theorem modalUltraproduct_atom (M : ∀ i, Unimodal.Model (W i) Atom)
    [∀ i, Nonempty (W i)] (U : Ultrafilter I) (f : ∀ i, W i) (p : Atom) :
    (modalUltraproduct M U).v (f : (U : Filter I).Product W) p ↔
      ∀ᶠ i in (U : Filter I), (M i).v (f i) p := by
  rfl

/-- Accessibility clause of Blue Book Def. 2.70(iii)
(2010 fourth corrected printing, p. 105), for basic unimodal ultraproducts. -/
theorem modalUltraproduct_rel (M : ∀ i, Unimodal.Model (W i) Atom)
    [∀ i, Nonempty (W i)] (U : Ultrafilter I) (f g : ∀ i, W i) :
    (modalUltraproduct M U).toFrame.rel
      (f : (U : Filter I).Product W) (g : (U : Filter I).Product W) ↔
      ∀ᶠ i in (U : Filter I), (M i).toFrame.rel (f i) (g i) := by
  rfl

/-- Auxiliary modal Łoś equivalence for Blue Book Thm. 2.75
(2010 fourth corrected printing, pp. 107–108), basic unimodal specialization.
This combines Prop. 2.47(i) (p. 85) with Thm. A.19 (pp. 493–494), as used
in the book's ultraproduct argument; it is not a new proof of Łoś's theorem.
No saturation, countability, or finiteness of the language is assumed. -/
theorem satisfies_modalUltraproduct (M : ∀ i, Unimodal.Model (W i) Atom)
    [∀ i, Nonempty (W i)] (U : Ultrafilter I)
    (φ : Unimodal.Proposition Atom) (f : ∀ i, W i) :
    Satisfies (modalUltraproduct M U) (f : (U : Filter I).Product W) φ ↔
      ∀ᶠ i in (U : Filter I), Satisfies (M i) (f i) φ := by
  let : ∀ i, (language Atom).Structure (W i) := fun i => toStructure (M i)
  refine (standardTranslation_correct (modalUltraproduct M U) φ _).trans
    (Iff.trans ?_ (Filter.eventually_congr (Filter.Eventually.of_forall fun i =>
      (standardTranslation_correct (M i) φ (f i)).symm)))
  unfold holds modalUltraproduct
  rw [toStructure_fromStructure]
  exact Ultraproduct.realize_formula_cast (standardTranslation φ) (fun _ => f)

end ModalCharacterization
