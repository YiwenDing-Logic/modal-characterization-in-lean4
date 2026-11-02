/-
Modal Characterization in Lean 4. Released under Apache-2.0; see LICENSE.
Reuses CSLib's LTS bisimulation API (Fabrizio Montesi, Thomas Waring).
Related existing HML invariance: Fabrizio Montesi, Marco Peressotti, Alexandre Rademaker.
Foundation's BisimulationUnder.forces_iff is related prior cross-model work.
The proof below follows Blackburn, de Rijke, Venema, Modal Logic (2010 printing).
This is an adaptation to our selected interface, not a first formalization claim.
-/
module

public import Cslib.Logics.Modal.Unimodal.Basic
public import Cslib.Foundations.Semantics.LTS.Bisimulation

@[expose] public section

namespace ModalCharacterization

open Cslib.Logic.Modal

universe u v w
variable {Atom : Type u} {W : Type v} {W' : Type w}

/-- Implementation adapter: regard a Kripke relation as a single-label transition system. -/
def modelLTS (M : Unimodal.Model W Atom) : Cslib.LTS W Unit where
  Tr x _ y := M.toFrame.rel x y

/-- Blue Book Def. 2.16 (2010 printing, pp. 64–65), basic unimodal specialization.
Includes the book's nonempty relation convention and agreement on every atom.
CSLib supplies the forth/back clauses, including for distinct world types. -/
structure IsModalBisimulation (M : Unimodal.Model W Atom) (N : Unimodal.Model W' Atom)
    (Z : W → W' → Prop) : Prop where
  nonempty : ∃ x y, Z x y
  atomic : ∀ ⦃x y⦄, Z x y → ∀ p, M.v x p ↔ N.v y p
  transitions : Cslib.LTS.IsBisimulation (modelLTS M) (modelLTS N) Z

/-- Implementation correspondence for Def. 2.16 (2010, pp. 64–65):
the adapter is exactly nonemptiness, atoms, forth and back. -/
theorem isModalBisimulation_iff (M : Unimodal.Model W Atom) (N : Unimodal.Model W' Atom)
    (Z : W → W' → Prop) :
    IsModalBisimulation M N Z ↔
      (∃ x y, Z x y) ∧
      (∀ x y, Z x y → ∀ p, M.v x p ↔ N.v y p) ∧
      (∀ x y, Z x y → ∀ x', M.toFrame.rel x x' →
        ∃ y', N.toFrame.rel y y' ∧ Z x' y') ∧
      (∀ x y, Z x y → ∀ y', N.toFrame.rel y y' →
        ∃ x', M.toFrame.rel x x' ∧ Z x' y') := by
  constructor
  · intro h
    refine ⟨h.nonempty, fun x y hxy => h.atomic hxy, ?_, ?_⟩
    · intro x y hxy x' hx
      exact h.transitions.follow_fst (μ := ()) hxy hx
    · intro x y hxy y' hy
      exact h.transitions.follow_snd (μ := ()) hxy hy
  · rintro ⟨hne, ha, hf, hb⟩
    refine ⟨hne, fun {x y} hxy => ha x y hxy, ?_⟩
    intro x y hxy μ
    exact ⟨hf x y hxy, hb x y hxy⟩

/-- Pointed bisimilarity of Blue Book Def. 2.16 (2010, pp. 64–65),
specialized to basic unimodal models. -/
def ModallyBisimilar (M : Unimodal.Model W Atom) (N : Unimodal.Model W' Atom)
    (x : W) (y : W') : Prop :=
  ∃ Z, IsModalBisimulation M N Z ∧ Z x y

/-- Auxiliary symmetry of pointed bisimilarity (Blue Book Def. 2.16,
2010 printing, pp. 64–65), used for complement closure in Thm. 2.75, p. 107.
Transpose the relation and exchange its forth and back conditions. -/
theorem ModallyBisimilar.symm {M : Unimodal.Model W Atom}
    {N : Unimodal.Model W' Atom} {x : W} {y : W'}
    (h : ModallyBisimilar M N x y) : ModallyBisimilar N M y x := by
  obtain ⟨Z, hZ, hxy⟩ := h
  obtain ⟨hne, ha, hf, hb⟩ := (isModalBisimulation_iff M N Z).mp hZ
  refine ⟨fun b a => Z a b, (isModalBisimulation_iff _ _ _).mpr ?_, hxy⟩
  obtain ⟨a, b, hab⟩ := hne
  exact ⟨⟨b, a, hab⟩, fun b a hab p => (ha a b hab p).symm,
    fun b a hab => hb a b hab, fun b a hab => hf a b hab⟩

/-- Blue Book Theorem 2.20 (2010 printing, p. 67), basic unimodal specialization
over arbitrary nonempty models. Follows the original structural induction:
atoms use agreement, Boolean cases use induction, diamond uses forth and back.
No finiteness, image-finiteness or saturation assumption is imposed. -/
theorem IsModalBisimulation.satisfies_iff
    {M : Unimodal.Model W Atom} {N : Unimodal.Model W' Atom}
    [Nonempty W] [Nonempty W'] {Z : W → W' → Prop}
    (hZ : IsModalBisimulation M N Z) {x : W} {y : W'} (hxy : Z x y)
    (φ : Unimodal.Proposition Atom) : Satisfies M x φ ↔ Satisfies N y φ := by
  induction φ generalizing x y with
  | atom p => exact hZ.atomic hxy p
  | false => exact Iff.rfl
  | not ψ ih => exact not_congr (ih hxy)
  | or ψ χ ihψ ihχ => exact or_congr (ihψ hxy) (ihχ hxy)
  | triangle op ψs ih =>
    have heq : Proposition.triangle op ψs =
        Cslib.Logic.HasDiamond.diamond (ψs default) := by
      cases op
      exact Proposition.unary_triangle_eq_dynDiamond ψs
    rw [heq]
    have hm : Satisfies M x (Cslib.Logic.HasDiamond.diamond (ψs default)) ↔
        ∃ x', M.toFrame.rel x x' ∧ Satisfies M x' (ψs default) :=
      Satisfies.diamond_iff_exists
    have hn : Satisfies N y (Cslib.Logic.HasDiamond.diamond (ψs default)) ↔
        ∃ y', N.toFrame.rel y y' ∧ Satisfies N y' (ψs default) :=
      Satisfies.diamond_iff_exists
    rw [hm, hn]
    constructor
    · rintro ⟨x', hx', hψ⟩
      obtain ⟨y', hy', hrel⟩ := hZ.transitions.follow_fst (μ := ()) hxy hx'
      exact ⟨y', hy', (ih default hrel).mp hψ⟩
    · rintro ⟨y', hy', hψ⟩
      obtain ⟨x', hx', hrel⟩ := hZ.transitions.follow_snd (μ := ()) hxy hy'
      exact ⟨x', hx', (ih default hrel).mpr hψ⟩

/-- Pointed form of Blue Book Theorem 2.20 (2010 printing, p. 67),
specialized to basic unimodal logic over nonempty models. -/
theorem ModallyBisimilar.satisfies_iff
    {M : Unimodal.Model W Atom} {N : Unimodal.Model W' Atom}
    [Nonempty W] [Nonempty W'] {x : W} {y : W'}
    (h : ModallyBisimilar M N x y) (φ : Unimodal.Proposition Atom) :
    Satisfies M x φ ↔ Satisfies N y φ := by
  obtain ⟨Z, hZ, hxy⟩ := h
  exact hZ.satisfies_iff hxy φ

end ModalCharacterization
