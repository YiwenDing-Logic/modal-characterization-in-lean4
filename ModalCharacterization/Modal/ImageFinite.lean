/-
Modal Characterization in Lean. Released under Apache-2.0; see LICENSE.
Image-finite corollaries of the project's modal-saturation theorem.
Prior CSLib HML work: Fabrizio Montesi, Marco Peressotti, Alexandre Rademaker.
This is not a first-formalization claim or a reproduction of the direct proof
of Blue Book Thm. 2.24; the result is derived here from modal saturation.
-/
module

public import ModalCharacterization.Modal.Saturation

@[expose] public section

namespace ModalCharacterization

open Cslib.Logic.Modal

universe u v w
variable {Atom : Type u} {W : Type v} {W' : Type w}

/-- Auxiliary finite-set compactness for Blue Book Def. 2.53 (2010 printing,
p. 92). On a finite set of worlds, finite satisfiability realizes the entire
formula set. The empty-world-set case is excluded by finite satisfiability
itself, since its empty finite subset also requires a witness. -/
theorem ModalFinitelySatisfiableIn.satisfiable_of_finite
    {M : Unimodal.Model W Atom} {Γ : Set (Unimodal.Proposition Atom)} {X : Set W}
    (h : ModalFinitelySatisfiableIn M Γ X) (hX : X.Finite) :
    ModalSatisfiableIn M Γ X := by
  classical
  by_contra hn
  have hfail : ∀ x : X, ∃ φ ∈ Γ, ¬Satisfies M x.val φ := by
    intro x
    by_contra hx
    push Not at hx
    exact hn ⟨x.val, x.property, hx⟩
  choose f hfΓ hf using hfail
  let : Fintype X := hX.fintype
  let Δ : Finset (Unimodal.Proposition Atom) := Finset.univ.image f
  obtain ⟨x, hx, hs⟩ := h Δ (by
    intro φ hφ
    obtain ⟨y, _, rfl⟩ := Finset.mem_image.mp hφ
    exact hfΓ y)
  exact hf ⟨x, hx⟩ (hs (f ⟨x, hx⟩) (Finset.mem_image.mpr ⟨⟨x, hx⟩, Finset.mem_univ _, rfl⟩))

/-- Derived bridge to Blue Book Def. 2.53 (2010 printing, pp. 92–93):
image-finite models are modally saturated. Image-finiteness is exactly CSLib's
existing LTS condition applied to `modelLTS`, not finiteness of all worlds.
This serves the saturation-based corollary of Thm. 2.24. -/
theorem isModallySaturated_of_imageFinite (M : Unimodal.Model W Atom)
    [h : (modelLTS M).ImageFinite] : IsModallySaturated M := by
  intro x Γ hΓ
  have : Finite {y | M.toFrame.rel x y} := h x ()
  exact hΓ.satisfiable_of_finite (Set.toFinite _)

/-- Conclusion of Blue Book Thm. 2.24 (2010 fourth corrected printing,
pp. 69–70), basic unimodal nonempty models, derived here via modal saturation
and Prop. 2.54 rather than the book's direct image-finite argument.
Related same-model HML results are already implemented in CSLib. -/
theorem modallyEquivalent_iff_bisimilar_of_imageFinite
    (M : Unimodal.Model W Atom) (N : Unimodal.Model W' Atom)
    [Nonempty W] [Nonempty W']
    [(modelLTS M).ImageFinite] [(modelLTS N).ImageFinite] (x : W) (y : W') :
    ModallyEquivalent M N x y ↔ ModallyBisimilar M N x y :=
  (isModallySaturated_of_imageFinite M).modallyEquivalent_iff_bisimilar
    (isModallySaturated_of_imageFinite N)

end ModalCharacterization
