/-
Modal Characterization in Lean. Released under Apache-2.0; see LICENSE.
Reuses Aaron Anderson's mathlib ultraproducts and the CSLib modal model interface.
-/
module

public import ModalCharacterization.FirstOrder.Ultrapower
public import ModalCharacterization.FirstOrder.UltraproductSaturation
public import ModalCharacterization.FirstOrder.LanguageCountability
public import ModalCharacterization.Modal.FirstOrderSaturation
public import ModalCharacterization.Modal.Ultraproduct
public import ModalCharacterization.Modal.StandardTranslation
public import ModalCharacterization.Modal.Saturation

@[expose] public section

namespace ModalCharacterization

open _root_.FirstOrder _root_.FirstOrder.Language Cslib.Logic.Modal

universe u v w z
variable {Atom : Type u} {W : Type v} {I : Type z}

/-- Blue Book Defs. 2.69–2.70 (2010 fourth corrected printing, p. 105),
specialized to the ultrapower of a nonempty basic unimodal model. The carrier
and first-order structure are mathlib's constant-family ultraproduct, read as
a Kripke model through `fromStructure`. -/
def modalUltrapower (M : Unimodal.Model W Atom) [Nonempty W] (U : Ultrafilter I) :
    Unimodal.Model ((U : Filter I).Product (fun _ : I => W)) Atom :=
  letI : (language Atom).Structure W := toStructure M
  fromStructure (inferInstance : (language Atom).Structure
    ((U : Filter I).Product (fun _ : I => W)))

/-- Auxiliary compatibility of the constant-family case of Blue Book
Defs. 2.69–2.70 (2010 fourth corrected printing, p. 105).
The general modal ultraproduct agrees with the existing ultrapower adapter. -/
theorem modalUltraproduct_const (M : Unimodal.Model W Atom) [Nonempty W]
    (U : Ultrafilter I) :
    modalUltraproduct (fun _ : I => M) U = modalUltrapower M U := by
  rfl

/-- Valuation clause of Blue Book Def. 2.70(ii) (2010 fourth corrected printing,
p. 105), specialized to a basic unimodal ultrapower. -/
theorem modalUltrapower_atom (M : Unimodal.Model W Atom) [Nonempty W]
    (U : Ultrafilter I) (f : I → W) (p : Atom) :
    (modalUltrapower M U).v (f : (U : Filter I).Product (fun _ : I => W)) p ↔
      ∀ᶠ i in (U : Filter I), M.v (f i) p := by
  rfl

/-- Accessibility clause of Blue Book Def. 2.70(iii) (2010 fourth corrected
printing, p. 105), specialized to a basic unimodal ultrapower. -/
theorem modalUltrapower_rel (M : Unimodal.Model W Atom) [Nonempty W]
    (U : Ultrafilter I) (f g : I → W) :
    (modalUltrapower M U).toFrame.rel
      (f : (U : Filter I).Product (fun _ : I => W))
      (g : (U : Filter I).Product (fun _ : I => W)) ↔
        ∀ᶠ i in (U : Filter I), M.toFrame.rel (f i) (g i) := by
  rfl

/-- Blue Book Prop. 2.71 (2010 fourth corrected printing, pp. 105–106),
for nonempty basic unimodal models: a point and its constant-function class
in any ultrapower satisfy the same modal formulas. The book leaves the proof
as Exercise 2.6.1; here local standard translation (Prop. 2.47(i)) and the
diagonal elementary embedding (Cor. A.21) supply it. No saturation or
countability assumption is needed. -/
theorem satisfies_modalUltrapower_diagonal
    (M : Unimodal.Model W Atom) [Nonempty W] (U : Ultrafilter I)
    (φ : Unimodal.Proposition Atom) (w : W) :
    Satisfies M w φ ↔ Satisfies (modalUltrapower M U)
      ((fun _ : I => w) : (U : Filter I).Product (fun _ : I => W)) φ := by
  let : (language Atom).Structure W := toStructure M
  refine (standardTranslation_correct M φ w).trans (Iff.trans ?_
    (standardTranslation_correct (modalUltrapower M U) φ _).symm)
  unfold holds modalUltrapower
  rw [toStructure_fromStructure]
  exact ((FirstOrder.ultrapowerDiagonal (language Atom) W U).map_formula
    (standardTranslation φ) (fun _ => w)).symm

/-- Cor. A.21 (2010 fourth corrected printing, p. 494), transported to the
basic unimodal ultrapower representation for Detour Lemma 2.66(iii), p. 103.
Both first-order structures are explicit, even when carriers coincide.
The underlying function is exactly the constant-function quotient map. -/
def modalUltrapowerDiagonal (M : Unimodal.Model W Atom) [Nonempty W]
    (U : Ultrafilter I) :
    letI : (language Atom).Structure W := toStructure M
    @ElementaryEmbedding (language Atom) W
      ((U : Filter I).Product (fun _ : I => W))
      (toStructure M) (toStructure (modalUltrapower M U)) := by
  let : (language Atom).Structure W := toStructure M
  let : (language Atom).Structure ((U : Filter I).Product (fun _ : I => W)) :=
    toStructure (modalUltrapower M U)
  refine { toFun := fun a => ((fun _ : I => a) :
    (U : Filter I).Product (fun _ : I => W)), map_formula' := ?_ }
  intro n φ xs
  unfold modalUltrapower
  rw [toStructure_fromStructure]
  let : (language Atom).Structure ((U : Filter I).Product (fun _ : I => W)) :=
    @Ultraproduct.structure I (fun _ : I => W) U (language Atom) (fun _ => toStructure M)
  exact (FirstOrder.ultrapowerDiagonal (language Atom) W U).map_formula φ xs

/-- Auxiliary modal-equivalence transport for Blue Book Thm. 2.74
(2010 printing, p. 106), from Prop. 2.71. Complete proof: independent of
the deferred saturation theorem, with arbitrary index type and ultrafilter. -/
theorem modallyEquivalent_diagonal_iff
    {Atom : Type u} {W : Type v} {W' : Type w}
    (M : Unimodal.Model W Atom) (N : Unimodal.Model W' Atom)
    [Nonempty W] [Nonempty W'] {I : Type z} (U : Ultrafilter I)
    (x : W) (y : W') :
    ModallyEquivalent (modalUltrapower M U) (modalUltrapower N U)
      ((fun _ : I => x) : (U : Filter I).Product (fun _ : I => W))
      ((fun _ : I => y) : (U : Filter I).Product (fun _ : I => W')) ↔
        ModallyEquivalent M N x y := by
  refine modallyEquivalent_iff.trans (Iff.trans ?_ modallyEquivalent_iff.symm)
  exact forall_congr' fun φ =>
    iff_congr (satisfies_modalUltrapower_diagonal M U φ x).symm
      (satisfies_modalUltrapower_diagonal N U φ y).symm

/-- Reverse direction of Blue Book Thm. 2.74 (2010 printing, p. 106), basic
unimodal specialization, for any shared ultrafilter and index type. Complete
proof: bisimulation invariance and Prop. 2.71 suffice; no saturation is used. -/
theorem modallyEquivalent_of_bisimilar_ultrapowers
    {Atom : Type u} {W : Type v} {W' : Type w}
    (M : Unimodal.Model W Atom) (N : Unimodal.Model W' Atom)
    [Nonempty W] [Nonempty W'] {I : Type z} (U : Ultrafilter I)
    (x : W) (y : W')
    (h : ModallyBisimilar (modalUltrapower M U) (modalUltrapower N U)
      ((fun _ : I => x) : (U : Filter I).Product (fun _ : I => W))
      ((fun _ : I => y) : (U : Filter I).Product (fun _ : I => W'))) :
    ModallyEquivalent M N x y := by
  apply (modallyEquivalent_diagonal_iff M N U x y).mp
  exact modallyEquivalent_iff.mpr (fun φ => h.satisfies_iff φ)

/-- Representation bridge for Lemma 2.73 and Blue Book Thm. 2.74
(2010 fourth corrected printing, p. 106), basic unimodal specialization.
Transports saturation across the existing first-order structure round trip. -/
theorem modalUltrapower_isOmegaSaturated
    {Atom : Type u} [Countable Atom] {W : Type v}
    (M : Unimodal.Model W Atom) [Nonempty W]
    {I : Type z} [Nonempty I] (U : Ultrafilter I)
    (hU : ¬ CountableInterFilter (U : Filter I)) :
    letI : (language Atom).Structure ((U : Filter I).Product (fun _ : I => W)) :=
      toStructure (modalUltrapower M U)
    FirstOrder.IsOmegaSaturated (language Atom)
      ((U : Filter I).Product (fun _ : I => W)) := by
  let : (language Atom).Structure W := toStructure M
  unfold modalUltrapower
  rw [toStructure_fromStructure]
  exact FirstOrder.ultrapower_isOmegaSaturated (language Atom) W U hU

/-- Blue Book Thm. 2.74 (2010 fourth corrected printing, pp. 106–107), basic unimodal
countable-language scope. The forward direction uses the book's chosen index ℕ
and one shared ultrafilter; this stronger witness restriction implies the book's
unrestricted existential conclusion. The reverse direction above handles any
index type. Uses Lemma 2.73 and the saturated-model Hennessy–Milner theorem. -/
theorem modallyEquivalent_iff_exists_bisimilar_nat_ultrapowers
    {Atom : Type u} [Countable Atom] {W : Type v} {W' : Type w}
    (M : Unimodal.Model W Atom) (N : Unimodal.Model W' Atom)
    [Nonempty W] [Nonempty W'] (x : W) (y : W') :
    ModallyEquivalent M N x y ↔
      ∃ U : Ultrafilter ℕ,
        ModallyBisimilar (modalUltrapower M U) (modalUltrapower N U)
          ((fun _ : ℕ => x) : (U : Filter ℕ).Product (fun _ : ℕ => W))
          ((fun _ : ℕ => y) : (U : Filter ℕ).Product (fun _ : ℕ => W')) := by
  constructor
  · intro h
    let U := Filter.hyperfilter ℕ
    have hU : ¬ CountableInterFilter (U : Filter ℕ) :=
      FirstOrder.nat_hyperfilter_not_countableInterFilter
    refine ⟨U, ?_⟩
    apply (modallyEquivalent_iff_bisimilar_of_isOmegaSaturated
      (modalUltrapower M U) (modalUltrapower N U)
      (modalUltrapower_isOmegaSaturated M U hU)
      (modalUltrapower_isOmegaSaturated N U hU)).mp
    exact (modallyEquivalent_diagonal_iff M N U x y).mpr h
  · rintro ⟨U, h⟩
    exact modallyEquivalent_of_bisimilar_ultrapowers M N U x y h

/-- Book-shaped existential formulation of Blue Book Thm. 2.74 (2010 fourth corrected printing,
pp. 106–107), for the agreed countable basic unimodal language. Both ultrapowers
use one common index type and ultrafilter. A small index type suffices because
the forward proof explicitly uses ℕ; the reverse lemma is universe-polymorphic.
No saturation or ultrapower-bisimilarity hypothesis is assumed. -/
theorem modallyEquivalent_iff_exists_bisimilar_ultrapowers
    {Atom : Type u} [Countable Atom] {W : Type v} {W' : Type w}
    (M : Unimodal.Model W Atom) (N : Unimodal.Model W' Atom)
    [Nonempty W] [Nonempty W'] (x : W) (y : W') :
    ModallyEquivalent M N x y ↔
      ∃ (I : Type) (U : Ultrafilter I),
        ModallyBisimilar (modalUltrapower M U) (modalUltrapower N U)
          ((fun _ : I => x) : (U : Filter I).Product (fun _ : I => W))
          ((fun _ : I => y) : (U : Filter I).Product (fun _ : I => W')) := by
  constructor
  · intro h
    obtain ⟨U, hU⟩ :=
      (modallyEquivalent_iff_exists_bisimilar_nat_ultrapowers M N x y).mp h
    exact ⟨ℕ, U, hU⟩
  · rintro ⟨I, U, h⟩
    exact modallyEquivalent_of_bisimilar_ultrapowers M N U x y h

end ModalCharacterization
