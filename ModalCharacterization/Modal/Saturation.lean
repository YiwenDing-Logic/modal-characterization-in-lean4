/-
Modal Characterization in Lean 4. Released under Apache-2.0; see LICENSE.
Follows Blackburn, de Rijke, Venema, Modal Logic (2010 fourth corrected printing).
Reuses CSLib's modal theory and finite-conjunction semantics (Fabrizio Montesi,
Marianna Girlando) and the project's CSLib LTS bisimulation adapter.
Related image-finite HML results are by Fabrizio Montesi, Marco Peressotti,
and Alexandre Rademaker; this is not a first-formalization claim.
-/
module

public import ModalCharacterization.Modal.Bisimulation
public import Mathlib.Data.Finset.Basic

@[expose] public section

namespace ModalCharacterization

open Cslib.Logic.Modal

universe u v w
variable {Atom : Type u} {W : Type v} {W' : Type w}

/-- Cross-model modal equivalence used in Blue Book Prop. 2.54 (2010 printing, p. 93).
Implementation adapter for basic unimodal models: reuse CSLib's sets of true formulas,
allowing the two world types to differ. -/
def ModallyEquivalent (M : Unimodal.Model W Atom) (N : Unimodal.Model W' Atom)
    (x : W) (y : W') : Prop :=
  theory M x = theory N y

/-- Semantic interface for the cross-model relation in Prop. 2.54 (2010, p. 93):
equality of theories means agreement on every modal formula. -/
theorem modallyEquivalent_iff {M : Unimodal.Model W Atom} {N : Unimodal.Model W' Atom}
    {x : W} {y : W'} :
    ModallyEquivalent M N x y ↔
      ∀ φ : Unimodal.Proposition Atom, Satisfies M x φ ↔ Satisfies N y φ :=
  Set.ext_iff

/-- Basic unimodal satisfiability in a set, Blue Book Def. 2.53 (2010 printing, p. 92).
One world in `X` must satisfy all formulas in `Γ`, including when `Γ` is empty. -/
def ModalSatisfiableIn (M : Unimodal.Model W Atom)
    (Γ : Set (Unimodal.Proposition Atom)) (X : Set W) : Prop :=
  ∃ x ∈ X, ∀ φ ∈ Γ, Satisfies M x φ

/-- Basic unimodal finite satisfiability in a set, Blue Book Def. 2.53
(2010 printing, p. 92). Finite subsets are represented by `Finset`, including the
empty subset; the witness may depend on the finite subset. -/
def ModalFinitelySatisfiableIn (M : Unimodal.Model W Atom)
    (Γ : Set (Unimodal.Proposition Atom)) (X : Set W) : Prop :=
  ∀ Δ : Finset (Unimodal.Proposition Atom), (∀ φ ∈ Δ, φ ∈ Γ) →
    ∃ x ∈ X, ∀ φ ∈ Δ, Satisfies M x φ

/-- Blue Book Def. 2.53 (2010 printing, pp. 92–93), basic unimodal specialization.
Every set of formulas finitely satisfiable among the successors of any world is
realized by one successor in the same model. There is no cardinality restriction
on the set of formulas or the world domain. -/
def IsModallySaturated (M : Unimodal.Model W Atom) : Prop :=
  ∀ x Γ, ModalFinitelySatisfiableIn M Γ {y | M.toFrame.rel x y} →
    ModalSatisfiableIn M Γ {y | M.toFrame.rel x y}

/-- Auxiliary step making explicit the last inference of Blue Book Prop. 2.54
(2010 printing, p. 93): realizing the full theory of a world gives modal equivalence.
The reverse inclusion uses negation, not merely the positive atomic theory. -/
theorem modallyEquivalent_of_theory_subset
    {M : Unimodal.Model W Atom} {N : Unimodal.Model W' Atom} {x : W} {y : W'}
    (h : theory M x ⊆ theory N y) : ModallyEquivalent M N x y := by
  classical
  apply modallyEquivalent_iff.mpr
  intro φ
  constructor
  · exact fun hφ => h hφ
  · intro hφ
    by_contra hn
    have hnot : Satisfies N y (.not φ) := h (a := .not φ) (show Satisfies M x (.not φ) from hn)
    exact hnot hφ

/-- Auxiliary forth step of Blue Book Prop. 2.54 (2010 printing, p. 93),
basic unimodal specialization. Transfer each finite conjunction under diamond,
then realize the successor's full theory using saturation of the target model. -/
theorem IsModallySaturated.exists_successor_modallyEquivalent
    {M : Unimodal.Model W Atom} {N : Unimodal.Model W' Atom}
    (hN : IsModallySaturated N) {x : W} {y : W'}
    (hxy : ModallyEquivalent M N x y) {x' : W} (hx : M.toFrame.rel x x') :
    ∃ y', N.toFrame.rel y y' ∧ ModallyEquivalent M N x' y' := by
  have hfin : ModalFinitelySatisfiableIn N (theory M x') {y' | N.toFrame.rel y y'} := by
    intro Δ hΔ
    have hconj : Satisfies M x' (Cslib.Logic.finiteAnd Δ.toList) :=
      Satisfies.finiteAnd_iff_forall.mpr fun φ hφ => hΔ φ (Finset.mem_toList.mp hφ)
    have hdiamond : Satisfies M x
        (Cslib.Logic.HasDiamond.diamond (Cslib.Logic.finiteAnd Δ.toList)) :=
      Satisfies.diamond_iff_exists.mpr ⟨x', hx, hconj⟩
    obtain ⟨y', hy', hs⟩ := Satisfies.diamond_iff_exists.mp
      ((modallyEquivalent_iff.mp hxy _).mp hdiamond)
    refine ⟨y', hy', fun φ hφ => ?_⟩
    exact Satisfies.finiteAnd_iff_forall.mp hs φ (Finset.mem_toList.mpr hφ)
  obtain ⟨y', hy', hs⟩ := hN y (theory M x') hfin
  exact ⟨y', hy', modallyEquivalent_of_theory_subset (fun _ hφ => hs _ hφ)⟩

/-- Blue Book Prop. 2.54 (2010 printing, p. 93), basic unimodal specialization
over nonempty models with independently sized world types. The relation is modal
equivalence, as in the book; the given pair witnesses its nonemptiness. Forth uses
the target's saturation and back uses the source's saturation. -/
theorem IsModallySaturated.bisimilar_of_modallyEquivalent
    {M : Unimodal.Model W Atom} {N : Unimodal.Model W' Atom}
    [Nonempty W] [Nonempty W'] (hM : IsModallySaturated M) (hN : IsModallySaturated N)
    {x : W} {y : W'} (hxy : ModallyEquivalent M N x y) :
    ModallyBisimilar M N x y := by
  refine ⟨ModallyEquivalent M N, ⟨⟨x, y, hxy⟩, ?_, ?_⟩, hxy⟩
  · intro a b hab p
    exact modallyEquivalent_iff.mp hab (.atom p)
  · intro a b hab μ
    constructor
    · intro a' ha'
      exact hN.exists_successor_modallyEquivalent hab ha'
    · intro b' hb'
      obtain ⟨a', ha', hrel⟩ := hM.exists_successor_modallyEquivalent
        (show ModallyEquivalent N M b a from Eq.symm hab) hb'
      exact ⟨a', ha', Eq.symm hrel⟩

/-- Derived biconditional combining Blue Book Prop. 2.54 (2010 printing, p. 93)
with Thm. 2.20 (p. 67), for basic unimodal nonempty modally saturated models.
No image-finiteness or existence of saturated extensions is assumed or proved. -/
theorem IsModallySaturated.modallyEquivalent_iff_bisimilar
    {M : Unimodal.Model W Atom} {N : Unimodal.Model W' Atom}
    [Nonempty W] [Nonempty W'] (hM : IsModallySaturated M) (hN : IsModallySaturated N)
    {x : W} {y : W'} :
    ModallyEquivalent M N x y ↔ ModallyBisimilar M N x y := by
  constructor
  · exact hM.bisimilar_of_modallyEquivalent hN
  · intro h
    exact modallyEquivalent_iff.mpr (fun φ => h.satisfies_iff φ)

end ModalCharacterization
