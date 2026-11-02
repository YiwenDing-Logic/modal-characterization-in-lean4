/-
Modal Characterization in Lean. Released under Apache-2.0; see LICENSE.
Reuses Aaron Anderson's mathlib model-theoretic encoding/countability APIs.
-/
module

public import ModalCharacterization.FirstOrder.ModalLanguage
public import Mathlib.ModelTheory.Encoding

@[expose] public section

namespace ModalCharacterization

open _root_.FirstOrder _root_.FirstOrder.Language

universe u v

/-- Auxiliary for the countable-language premise of Blue Book Lemma 2.73
(2010 fourth corrected printing, p. 106). The basic unimodal relation symbols
are a copy of the atoms together with one accessibility symbol. -/
instance countableRelationSymbols (Atom : Type u) [Countable Atom] :
    Countable (Σ n, RelationSymbol Atom n) := by
  let f : Option Atom → Σ n, RelationSymbol Atom n := fun p =>
    match p with
    | none => ⟨2, .access⟩
    | some a => ⟨1, .atom a⟩
  apply Function.Surjective.countable (f := f)
  rintro ⟨n, r⟩
  cases r with
  | atom p => exact ⟨some p, rfl⟩
  | access => exact ⟨none, rfl⟩

/-- Auxiliary for Blue Book Lemma 2.73 / Thm. 2.74 (2010 printing, p. 106):
countably many propositional letters give a countable correspondence language.
This places no restriction on the cardinality of the world domain. -/
instance countableLanguageSymbols (Atom : Type u) [Countable Atom] :
    Countable (language Atom).Symbols := by
  change Countable ((Σ _ : ℕ, Empty) ⊕ (Σ n, RelationSymbol Atom n))
  infer_instance

/-- Auxiliary for the finite-parameter one-types of Blue Book Lemma 2.73
(2010 printing, p. 106). Naming finitely many elements of an arbitrary world
domain leaves the one-variable formula type countable, by mathlib's encoding
instances. This counts formulas; it does not prove realization or saturation. -/
theorem countable_parameterFormulas (Atom : Type u) [Countable Atom]
    {W : Type v} (A : Set W) (hA : A.Finite) :
    Countable ((language Atom)[[A]].Formula (Fin 1)) := by
  let := hA.fintype
  infer_instance

end ModalCharacterization
