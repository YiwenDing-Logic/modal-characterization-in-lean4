/-
Modal Characterization in Lean 4. Released under Apache-2.0; see LICENSE.
Uses the existing mathlib first-order semantics and CSLib-based modal adapters.
Source: Blackburn, de Rijke, Venema, Modal Logic, fourth printing (2010).
Only the easy direction is proved here; no claim of a new mathematical result.
-/
module

public import ModalCharacterization.Modal.StandardTranslation

/-! Semantic interfaces for the basic unimodal specialization of Blue Book Theorem 2.68.
Model universes are explicit parameters: `Type v` ranges over all carriers at that level,
not a fixed carrier or a finite/countable subclass. Lean does not quantify over universe
levels inside propositions. The cross-universe helper below uses the same modal witness
and equivalence hypotheses at each of the two levels. The converse is not proved here. -/

@[expose] public section

namespace ModalCharacterization

universe u v w
variable {Atom : Type u}

/-- Semantic equivalence used in Blue Book Theorem 2.68 (2010, pp. 103–104).
Quantifies over every nonempty first-order structure at model universe `v` and every
assignment to the one available free variable; no Kripke presentation is assumed. -/
def FormulaSemanticallyEquiv (α β : (language Atom).Formula (Fin 1)) : Prop :=
  ∀ (W : Type v) [Nonempty W] (S : (language Atom).Structure W) (x : W),
    letI := S
    α.Realize (fun _ => x) ↔ β.Realize (fun _ => x)

/-- Modal expressibility in the standard-translation sense of Blue Book Theorem 2.68
(2010, pp. 103–104), at model universe `v`. The single modal witness precedes all models. -/
def ModallyExpressible (α : (language Atom).Formula (Fin 1)) : Prop :=
  ∃ φ : Cslib.Logic.Modal.Unimodal.Proposition Atom,
    FormulaSemanticallyEquiv.{u, v} α (standardTranslation φ)

/-- Bisimulation invariance for the basic unimodal specialization of Blue Book
Theorem 2.68 (2010, pp. 103–104), between arbitrary nonempty carriers at universe `v`.
The two models and their valuations are independent. -/
def BisimulationInvariant (α : (language Atom).Formula (Fin 1)) : Prop :=
  ∀ (W W' : Type v) [Nonempty W] [Nonempty W']
    (M : Cslib.Logic.Modal.Unimodal.Model W Atom)
    (N : Cslib.Logic.Modal.Unimodal.Model W' Atom) (x : W) (y : W'),
    ModallyBisimilar M N x y → (holds M α x ↔ holds N α y)

/-- Implementation helper: all-structure equivalence specializes to a Kripke model's
explicit first-order interpretation. -/
theorem FormulaSemanticallyEquiv.holds_iff
    {α β : (language Atom).Formula (Fin 1)} (h : FormulaSemanticallyEquiv.{u, v} α β)
    {W : Type v} [Nonempty W] (M : Cslib.Logic.Modal.Unimodal.Model W Atom) (x : W) :
    holds M α x ↔ holds M β x :=
  h W (toStructure M) x

/-- Auxiliary cross-universe form of the easy direction of Blue Book Theorem 2.68
(2010, pp. 103–104). The same modal formula represents `α` at both model levels.
Compose semantic equivalence with Theorem 2.20 and Prop. 2.47(i); no converse is asserted. -/
theorem ModallyBisimilar.formula_iff_of_equiv_standardTranslation
    {α : (language Atom).Formula (Fin 1)}
    {φ : Cslib.Logic.Modal.Unimodal.Proposition Atom}
    (hleft : FormulaSemanticallyEquiv.{u, v} α (standardTranslation φ))
    (hright : FormulaSemanticallyEquiv.{u, w} α (standardTranslation φ))
    {W : Type v} {W' : Type w} [Nonempty W] [Nonempty W']
    {M : Cslib.Logic.Modal.Unimodal.Model W Atom}
    {N : Cslib.Logic.Modal.Unimodal.Model W' Atom} {x : W} {y : W'}
    (h : ModallyBisimilar M N x y) : holds M α x ↔ holds N α y := by
  exact (hleft.holds_iff M x).trans
    ((h.standardTranslation_iff φ).trans (hright.holds_iff N y).symm)

/-- Easy direction ONLY of Blue Book Theorem 2.68 (2010 printing, pp. 103–104),
specialized to basic unimodal logic over all nonempty models at arbitrary universe `v`:
equivalence to one standard translation implies bisimulation invariance.
Uses Theorem 2.20 and Prop. 2.47(i); this does not prove the converse characterization. -/
theorem ModallyExpressible.bisimulationInvariant
    {α : (language Atom).Formula (Fin 1)} (h : ModallyExpressible.{u, v} α) :
    BisimulationInvariant.{u, v} α := by
  obtain ⟨φ, hφ⟩ := h
  intro W W' _ _ M N x y hxy
  exact hxy.formula_iff_of_equiv_standardTranslation hφ hφ

end ModalCharacterization
