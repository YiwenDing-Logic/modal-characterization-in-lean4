/-
Modal Characterization in Lean. Released under Apache-2.0; see LICENSE.
Uses mathlib and, in the modal adapter, CSLib (Fabrizio Montesi, Marianna Girlando).
Blue Book: Blackburn, de Rijke, Venema, Modal Logic, fourth printing (2010).
Foundation's historical standard translation by Mashu Noguchi is prior work;
no Foundation code is copied, ported or imported here.
-/
module

public import Mathlib.ModelTheory.Basic

@[expose] public section

namespace ModalCharacterization

universe u

/-- Blue Book Def. 2.44 (2010 printing, p. 84), basic unimodal specialization:
one unary predicate per atom and one binary accessibility relation. -/
inductive RelationSymbol (Atom : Type u) : Nat → Type u
  | atom (p : Atom) : RelationSymbol Atom 1
  | access : RelationSymbol Atom 2

/-- Correspondence language of Blue Book Def. 2.44 (2010 printing, p. 84),
basic unimodal specialization. No function symbols; mathlib supplies equality. -/
def language (Atom : Type u) : FirstOrder.Language where
  Functions := fun _ => Empty
  Relations := RelationSymbol Atom

end ModalCharacterization
