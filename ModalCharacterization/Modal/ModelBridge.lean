/-
Modal Characterization in Lean 4. Released under Apache-2.0; see LICENSE.
Uses mathlib and, in the modal adapter, CSLib (Fabrizio Montesi, Marianna Girlando).
Blue Book: Blackburn, de Rijke, Venema, Modal Logic, fourth printing (2010).
Foundation's historical standard translation by Mashu Noguchi is prior work;
no Foundation code is copied, ported or imported here.
-/
module

public import ModalCharacterization.FirstOrder.ModalLanguage
public import Cslib.Logics.Modal.Unimodal.Basic
public import Mathlib.ModelTheory.Semantics

@[expose] public section

namespace ModalCharacterization

universe u v

variable {Atom : Type u} {W : Type v}

/-- Interpret the signature on the original, nonempty world domain. -/
@[instance_reducible]
def toStructure (M : Cslib.Logic.Modal.Unimodal.Model W Atom) [Nonempty W] :
    (language Atom).Structure W where
  funMap := fun f => Empty.elim f
  RelMap := fun r xs => match r with
    | .atom p => M.v (xs 0) p
    | .access => M.toFrame.rel (xs 0) (xs 1)

/-- Recover a Kripke model from an arbitrary structure, explicitly supplied. -/
def fromStructure (S : (language Atom).Structure W) [Nonempty W] :
    Cslib.Logic.Modal.Unimodal.Model W Atom where
  toFrame := Cslib.Frame.ofRelation (fun w z => S.RelMap .access ![w, z])
  v := fun w p => S.RelMap (.atom p) (fun _ => w)

/-- A genuine mathlib formula for the atom at the single free variable. -/
def atomFormula (p : Atom) : (language Atom).Formula (Fin 1) :=
  FirstOrder.Language.Relations.formula₁ (L := language Atom)
    (RelationSymbol.atom p) (.var 0)

/-- Formula evaluation carries an explicit model; the structure is local. -/
def holds (M : Cslib.Logic.Modal.Unimodal.Model W Atom) [Nonempty W]
    (φ : (language Atom).Formula (Fin 1)) (w : W) : Prop :=
  letI : (language Atom).Structure W := toStructure M
  φ.Realize (fun _ => w)

/-- Atomic interpretation helper for Blue Book Prop. 2.47(i) (2010 printing, p. 85). -/
theorem atom_preserved (M : Cslib.Logic.Modal.Unimodal.Model W Atom) [Nonempty W]
    (p : Atom) (w : W) : holds M (atomFormula p) w ↔ M.v w p := by
  rfl

/-- Accessibility interpretation helper for Blue Book Def. 2.44 (2010 printing, p. 84). -/
theorem access_preserved (M : Cslib.Logic.Modal.Unimodal.Model W Atom) [Nonempty W]
    (w z : W) : (toStructure M).RelMap .access ![w, z] ↔ M.toFrame.rel w z := by
  rfl

/-- Implementation helper: model round trip preserves atomic truth. -/
theorem model_roundtrip_atom (M : Cslib.Logic.Modal.Unimodal.Model W Atom)
    [Nonempty W] (w : W) (p : Atom) :
    (fromStructure (toStructure M)).v w p ↔ M.v w p := by
  rfl

/-- Implementation helper: model round trip preserves accessibility. -/
theorem model_roundtrip_access (M : Cslib.Logic.Modal.Unimodal.Model W Atom)
    [Nonempty W] (w z : W) :
    (fromStructure (toStructure M)).toFrame.rel w z ↔ M.toFrame.rel w z := by
  rfl

/-- All relation interpretations, on arbitrary tuples, survive the reverse round trip. -/
theorem structure_roundtrip (S : (language Atom).Structure W) [Nonempty W]
    {n : Nat} (r : (language Atom).Relations n) (xs : Fin n → W) :
    (toStructure (fromStructure S)).RelMap r xs ↔ S.RelMap r xs := by
  cases r with
  | atom p =>
    change S.RelMap (.atom p) (fun _ => xs 0) ↔ S.RelMap (.atom p) xs
    have h : (fun _ : Fin 1 => xs 0) = xs := by
      funext i
      exact congrArg xs (Subsingleton.elim 0 i)
    rw [h]
  | access =>
    change S.RelMap .access ![xs 0, xs 1] ↔ S.RelMap .access xs
    have h : ![xs 0, xs 1] = xs := by
      funext i
      refine Fin.cases ?_ (fun j => ?_) i
      · rfl
      · have hj : j = 0 := Subsingleton.elim _ _
        subst j
        rfl
    rw [h]

/-- Representation helper for Blue Book Prop. 2.71 (2010 fourth corrected
printing, p. 105): interpreting a first-order correspondence-language structure
as a basic unimodal model and back recovers the entire original structure.
This upgrades `structure_roundtrip` from relations to structure equality, so
first-order realization lemmas apply to the recovered modal model. -/
theorem toStructure_fromStructure (S : (language Atom).Structure W) [Nonempty W] :
    toStructure (fromStructure S) = S := by
  apply FirstOrder.Language.Structure.ext
  · funext n f
    exact Empty.elim f
  · funext n r xs
    exact propext (structure_roundtrip S r xs)

end ModalCharacterization
