/-
Modal Characterization in Lean. Released under Apache-2.0; see LICENSE.
Reuses mathlib's ultraproduct semantics and elementary maps (Aaron Anderson).
-/
module

public import Mathlib.ModelTheory.ElementaryMaps
public import Mathlib.ModelTheory.Ultraproducts

/-!
# The diagonal elementary embedding into an ultrapower

`ModalCharacterization.FirstOrder.ultrapowerDiagonal` sends an element of a nonempty
first-order structure to the equivalence class of its constant function in an ultrapower.
Its elementarity follows directly from mathlib's formula-level Łoś theorem. The existing
`FirstOrder.Language.ElementaryEmbedding` API then supplies preservation of formulas,
sentences and theories, as well as injectivity.

The language, structure and index type have independent universes. No countability,
saturation or nonprincipality assumption is required. This module depends only on mathlib.

## References

Blackburn, de Rijke and Venema, *Modal Logic*, 2010 fourth corrected printing,
Corollary A.21 (p. 494), using Theorem A.19 (pp. 493–494).
-/

@[expose] public section

namespace ModalCharacterization.FirstOrder

open _root_.FirstOrder _root_.FirstOrder.Language

universe u v w z
variable (L : Language.{u, v}) (M : Type w) [L.Structure M] [Nonempty M]
variable {I : Type z} (U : Ultrafilter I)

/-- Blue Book Cor. A.21 (2010 fourth corrected printing, p. 494): the diagonal
map into an ultrapower is elementary. It sends an element to the class of its
constant function. The proof specializes mathlib's formula-level Łoś theorem
(Blue Book Thm. A.19, pp. 493–494), exactly as in the book. This auxiliary for
Prop. 2.71 and Thm. 2.74 requires neither countability nor saturation. The supplied
ultrafilter is proper, so an empty index type cannot supply such a `U`. -/
def ultrapowerDiagonal :
    M ↪ₑ[L] (U : Filter I).Product (fun _ : I => M) where
  toFun := fun a => ((fun _ : I => a) : (U : Filter I).Product (fun _ : I => M))
  map_formula' := by
    intro n φ x
    exact (Ultraproduct.realize_formula_cast (M := fun _ : I => M) (u := U)
      φ (fun j _ => x j)).trans Filter.eventually_const

end ModalCharacterization.FirstOrder
