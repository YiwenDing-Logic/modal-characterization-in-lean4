/-
Relation interface for Blue Book §2.5 (2010 fourth corrected printing).
Uses mathlib's relation and ultrafilter APIs (including Jeremy Avigad's relation APIs).
Related prior work: Mashu Noguchi's complex algebra in FFL/ModalLogic;
Yiming Xu and Michael Norrish's HOL4 ultrafilter extension formalization (2020).
No code from those independent developments is copied or imported here.
-/
module

public import Mathlib.Order.Filter.Partial
public import Mathlib.Order.Filter.Ultrafilter.Basic

@[expose] public section

namespace ModalCharacterization.UltrafilterRelation

universe u v
variable {W : Type u} {V : Type v}

/-- Blue Book Prop. 2.56 (2010 printing, p. 94), binary-relation duality.
Here the same argument is generalized to relations between different carriers:
mathlib's `core` is the box operation and `preimage` is the diamond operation. -/
theorem core_eq_compl_preimage_compl (R : SetRel W V) (X : Set V) :
    R.core X = (R.preimage Xᶜ)ᶜ := by
  ext x
  simp only [SetRel.mem_core, Set.mem_compl_iff, SetRel.mem_preimage]
  classical
  constructor
  · intro h ⟨y, hy, hxy⟩
    exact hy (h hxy)
  · intro h y hxy
    by_contra hy
    exact h ⟨y, hy, hxy⟩

/-- Interface check for Blue Book Def. 2.57 (2010 printing, p. 94).
`RTendsto'`, with its apostrophe, has exactly the required diamond condition.
This is an adapter to an existing definition, not a new frame definition. -/
theorem rtendsto'_iff_diamond (R : SetRel W V) (a : Ultrafilter W)
    (b : Ultrafilter V) :
    Filter.RTendsto' R (a : Filter W) (b : Filter V) ↔
      ∀ X ∈ b, R.preimage X ∈ a :=
  Filter.rtendsto'_def R a b

/-- Auxiliary box characterization of Def. 2.57, used in the proof of
Blue Book Prop. 2.59 (2010 printing, pp. 96–97; see also Exercise 2.5.5).
Both carriers are arbitrary; no finiteness, countability or seriality assumption.
The proof uses ultrafilter complement decisions and Prop. 2.56 duality. -/
theorem rtendsto'_iff_box (R : SetRel W V) (a : Ultrafilter W)
    (b : Ultrafilter V) :
    Filter.RTendsto' R (a : Filter W) (b : Filter V) ↔
      ∀ X, R.core X ∈ a → X ∈ b := by
  classical
  rw [rtendsto'_iff_diamond]
  constructor
  · intro h X hX
    by_contra hn
    have hp := h Xᶜ (Ultrafilter.compl_mem_iff_notMem.mpr hn)
    rw [core_eq_compl_preimage_compl] at hX
    exact (Ultrafilter.compl_mem_iff_notMem.mp hX) hp
  · intro h X hX
    by_contra hn
    have hc : R.core Xᶜ ∈ a := by
      rw [core_eq_compl_preimage_compl, compl_compl]
      exact Ultrafilter.compl_mem_iff_notMem.mpr hn
    exact (Ultrafilter.compl_mem_iff_notMem.mp (h Xᶜ hc)) hX

/-- Principal-point relation check, Blue Book equation (2.1)
(2010 printing, p. 95). Specializing the two carriers to one yields the
original relation exactly, in both directions. This does not assert a bounded morphism. -/
theorem rtendsto'_pure_iff (R : SetRel W V) (x : W) (y : V) :
    Filter.RTendsto' R ((pure x : Ultrafilter W) : Filter W)
      ((pure y : Ultrafilter V) : Filter V) ↔ (x, y) ∈ R := by
  rw [rtendsto'_iff_diamond]
  constructor
  · intro h
    have hs := h {y} (by simp)
    simpa [SetRel.mem_preimage] using hs
  · intro h X hX
    exact ⟨y, hX, h⟩

/-- Auxiliary successor existence for Blue Book Prop. 2.59 (2010 printing,
pp. 96–97). The box-family is the filter `a.rmap R`; adjoining `X` is its
infimum with the principal filter of `X`. Its properness packages the book's
finite-intersection argument, since the box-family is closed under finite meets.
Extend this proper filter using mathlib's ultrafilter theorem. -/
theorem exists_successor_mem (R : SetRel W V) (a : Ultrafilter W)
    (X : Set V) (hX : R.preimage X ∈ a) :
    ∃ b : Ultrafilter V,
      Filter.RTendsto' R (a : Filter W) (b : Filter V) ∧ X ∈ b := by
  classical
  let f := (a : Filter W).rmap R ⊓ Filter.principal X
  have hf : f.NeBot := by
    rw [← Filter.frequently_mem_iff_neBot]
    change ¬ R.core Xᶜ ∈ a
    rw [core_eq_compl_preimage_compl, compl_compl]
    exact fun hn => (Ultrafilter.compl_mem_iff_notMem.mp hn) hX
  let := hf
  refine ⟨Ultrafilter.of f, ?_, ?_⟩
  · apply (rtendsto'_iff_box R a _).mpr
    intro Y hY
    exact (le_trans (Ultrafilter.of_le f) inf_le_left) hY
  · exact (le_trans (Ultrafilter.of_le f) inf_le_right) (by simp)

end ModalCharacterization.UltrafilterRelation
