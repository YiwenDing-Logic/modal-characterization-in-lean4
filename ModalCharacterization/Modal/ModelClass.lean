/-
Modal Characterization in Lean. Released under Apache-2.0; see LICENSE.
Uses CSLib modal semantics and Aaron Anderson's mathlib ultraproduct theorem
through the project's standard-translation and ultraproduct adapters.
-/
module

public import ModalCharacterization.Modal.Ultrapower

@[expose] public section

namespace ModalCharacterization

open Cslib.Logic.Modal

universe u v

/-- Pointed model classes preceding Blue Book Thm. 2.75
(2010 fourth corrected printing, p. 107), basic unimodal specialization.
Membership ranges over all carriers at universe `v`, all models and all points.
A designated point ensures nonemptiness; worlds need not be finite or countable. -/
abbrev PointedModelClass (Atom : Type u) :=
  ∀ {W : Type v}, Unimodal.Model W Atom → W → Prop

namespace PointedModelClass

variable {Atom : Type u} (K : PointedModelClass.{u, v} Atom)

/-- Complement in all pointed models, as on Blue Book p. 107
(2010 fourth corrected printing), at the same fixed world universe. -/
def compl : PointedModelClass.{u, v} Atom := fun M x => ¬ K M x

/-- Definability by a set of formulas preceding Blue Book Thm. 2.75
(2010 fourth corrected printing, p. 107). The same formula set defines membership
for every pointed basic unimodal model at world universe `v`. -/
def IsModallyDefinable : Prop :=
  ∃ Γ : Set (Unimodal.Proposition Atom),
    ∀ {W : Type v} (M : Unimodal.Model W Atom) (x : W),
      K M x ↔ ∀ φ ∈ Γ, Satisfies M x φ

/-- Bisimulation closure preceding Blue Book Thm. 2.75
(2010 fourth corrected printing, p. 107), between arbitrary carriers at universe `v`. -/
def ClosedUnderBisimulations : Prop :=
  ∀ {W W' : Type v} (M : Unimodal.Model W Atom) (N : Unimodal.Model W' Atom)
    (x : W) (y : W'), K M x → ModallyBisimilar M N x y → K N y

/-- Ultraproduct closure preceding Blue Book Thm. 2.75
(2010 fourth corrected printing, p. 107), basic unimodal specialization.
Indices and component worlds range over `Type v`, so the product stays at `v`.
This is not restricted to constant families or countable index sets.
Smaller-universe indices require explicit transport when applying this interface. -/
def ClosedUnderUltraproducts : Prop :=
  ∀ {I : Type v} {W : I → Type v} (M : ∀ i, Unimodal.Model (W i) Atom)
    [∀ i, Nonempty (W i)] (U : Ultrafilter I) (x : ∀ i, W i),
    (∀ i, K (M i) (x i)) → K (modalUltraproduct M U) (x : (U : Filter I).Product W)

/-- Pointed ultrapower closure used in Blue Book Thm. 2.75(ii)
(2010 fourth corrected printing, p. 107). The designated point is the diagonal
constant-function class. Indices and worlds have the fixed universe `v`. -/
def ClosedUnderUltrapowers : Prop :=
  ∀ {I W : Type v} (M : Unimodal.Model W Atom) [Nonempty W]
    (U : Ultrafilter I) (x : W), K M x →
      K (modalUltrapower M U)
        ((fun _ : I => x) : (U : Filter I).Product (fun _ : I => W))

variable {K}

/-- Complement bisimulation closure, explicitly observed in the proof of
Blue Book Thm. 2.75 (2010 fourth corrected printing, p. 107).
Uses symmetry of bisimilarity, without modal-definability assumptions. -/
theorem ClosedUnderBisimulations.compl (h : K.ClosedUnderBisimulations) :
    ClosedUnderBisimulations (compl K) := by
  intro W W' M N x y hx hxy hy
  exact hx (h N M y x hy hxy.symm)

/-- Bisimulation part of Blue Book Thm. 2.75(i) → (ii)
(2010 fourth corrected printing, p. 107), via Thm. 2.20.
Basic unimodal models at a fixed arbitrary world universe. -/
theorem IsModallyDefinable.closedUnderBisimulations (h : K.IsModallyDefinable) :
    K.ClosedUnderBisimulations := by
  obtain ⟨Γ, hΓ⟩ := h
  intro W W' M N x y hx hxy
  let : Nonempty W := ⟨x⟩
  let : Nonempty W' := ⟨y⟩
  apply (hΓ N y).mpr
  intro φ hφ
  exact (hxy.satisfies_iff φ).mp ((hΓ M x).mp hx φ hφ)

/-- Ultraproduct part of Blue Book Thm. 2.75(i) → (ii)
(2010 fourth corrected printing, p. 107), using Prop. 2.47 and Łoś as in the book.
Applied separately to each formula, without requiring infinite-intersection closure. -/
theorem IsModallyDefinable.closedUnderUltraproducts (h : K.IsModallyDefinable) :
    K.ClosedUnderUltraproducts := by
  obtain ⟨Γ, hΓ⟩ := h
  intro I W M _ U x hx
  apply (hΓ (modalUltraproduct M U) _).mpr
  intro φ hφ
  apply (satisfies_modalUltraproduct M U φ x).mpr
  exact Filter.Eventually.of_forall fun i => (hΓ (M i) (x i)).mp (hx i) φ hφ

/-- Complement ultrapower part of Blue Book Thm. 2.75(i) → (ii)
(2010 fourth corrected printing, p. 107), using Prop. 2.71.
Reflection of each defining formula along the diagonal reflects class membership. -/
theorem IsModallyDefinable.compl_closedUnderUltrapowers (h : K.IsModallyDefinable) :
    ClosedUnderUltrapowers (compl K) := by
  obtain ⟨Γ, hΓ⟩ := h
  intro I W M _ U x hx hprod
  apply hx
  apply (hΓ M x).mpr
  intro φ hφ
  exact (satisfies_modalUltrapower_diagonal M U φ x).mpr
    ((hΓ (modalUltrapower M U) _).mp hprod φ hφ)

/-- Necessary direction ONLY of Blue Book Thm. 2.75
(2010 fourth corrected printing, p. 107), for basic unimodal pointed models
at arbitrary fixed world universe `v`, with index types at that same universe.
No countability or saturation assumption. This does not assert the converse. -/
theorem IsModallyDefinable.necessary (h : K.IsModallyDefinable) :
    K.ClosedUnderBisimulations ∧ K.ClosedUnderUltraproducts ∧
      ClosedUnderUltrapowers (compl K) :=
  ⟨h.closedUnderBisimulations, h.closedUnderUltraproducts,
    h.compl_closedUnderUltrapowers⟩

end PointedModelClass
end ModalCharacterization
