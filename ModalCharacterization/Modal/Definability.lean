/- Modal Characterization in Lean 4. Released under Apache-2.0; see LICENSE. -/
module

public import ModalCharacterization.Modal.ClassCompactness
public import ModalCharacterization.Modal.Compactness
public import ModalCharacterization.Modal.Ultrapower

@[expose] public section

namespace ModalCharacterization.PointedModelClass
open Cslib.Logic.Modal
universe v

/-- CONDITIONAL Blue Book Thm. 2.75 (2010 fourth corrected printing,
pp. 107–109), basic unimodal specialization at fixed world universe `v`.
The forward implication of Thm. 2.74 is an EXPLICIT premise `h274`, not proved
here: modally equivalent points have bisimilar diagonal points in ultrapowers
using one common small index type and ultrafilter. No experiment is imported.
The converse follows the book: modal consequences, Claim 1, Thm. 2.74, class
ultraproduct/bisimulation closure, and complement ultrapower closure.
Atoms lie in `Type`; absent a proof of `h274`, this is NOT an unconditional
definability characterization. The standard countable-language instance of
that premise is supplied by the production Thm. 2.74 in `modallyDefinable_iff`. -/
theorem modallyDefinable_iff_of_bisimilar_ultrapowers
    {Atom : Type}
    (h274 : ∀ {W W' : Type v} (M : Unimodal.Model W Atom)
      (N : Unimodal.Model W' Atom) [Nonempty W] [Nonempty W'] (x : W) (y : W'),
      ModallyEquivalent M N x y → ∃ (I : Type) (U : Ultrafilter I),
        ModallyBisimilar (modalUltrapower M U) (modalUltrapower N U)
          ((fun _ : I => x) : (U : Filter I).Product (fun _ : I => W))
          ((fun _ : I => y) : (U : Filter I).Product (fun _ : I => W')))
    (K : PointedModelClass.{0, v} Atom) :
    K.IsModallyDefinable ↔ K.ClosedUnderBisimulations ∧ K.ClosedUnderUltraproducts ∧
      ClosedUnderUltrapowers (compl K) := by
  classical
  refine ⟨fun h => h.necessary, ?_⟩
  rintro ⟨hB, hU, hC⟩
  let T : Set (Unimodal.Proposition Atom) :=
    {φ | ∀ {W : Type v} (M : Unimodal.Model W Atom) (x : W), K M x → Satisfies M x φ}
  refine ⟨T, ?_⟩
  intro W M x
  constructor
  · intro hx φ hφ
    exact hφ M x hx
  · intro hx
    obtain ⟨V, N, y, hy, hMN⟩ := exists_modallyEquivalent_of_modal_consequences
      hU hB M x (fun φ hφ => hx φ hφ)
    let : Nonempty W := ⟨x⟩
    let : Nonempty V := ⟨y⟩
    obtain ⟨I, U, hbis⟩ := h274 N M y x (Eq.symm hMN)
    have hN := hU.smallIndex hB (fun _ : I => N) U (fun _ => y) (fun _ => hy)
    have hM := hB (modalUltrapower N U) (modalUltrapower M U) _ _ hN hbis
    by_contra hn
    exact hC.smallIndex hB.compl M U x hn hM

/-- Single-formula definability preceding Blue Book Thm. 2.76
(2010 fourth corrected printing, pp. 107, 109), basic unimodal specialization.
One formula uniformly defines the pointed class on all carriers at universe `v`. -/
def IsDefinableByFormula {Atom : Type} (K : PointedModelClass.{0, v} Atom) : Prop :=
  ∃ φ : Unimodal.Proposition Atom,
    ∀ {W : Type v} (M : Unimodal.Model W Atom) (x : W), K M x ↔ Satisfies M x φ

/-- Auxiliary singleton-theory conversion for Blue Book Thm. 2.76
(2010 printing, p. 109); no compactness is needed in this direction. -/
theorem IsDefinableByFormula.isModallyDefinable
    {Atom : Type} {K : PointedModelClass.{0, v} Atom} (h : K.IsDefinableByFormula) :
    K.IsModallyDefinable := by
  obtain ⟨φ, hφ⟩ := h
  refine ⟨{φ}, ?_⟩
  intro W M x
  simpa using hφ M x

/-- Negation defines the complement, used in Blue Book Thm. 2.76(i) → (ii)
(2010 fourth corrected printing, p. 109), for pointed basic unimodal classes. -/
theorem IsDefinableByFormula.compl
    {Atom : Type} {K : PointedModelClass.{0, v} Atom} (h : K.IsDefinableByFormula) :
    IsDefinableByFormula (compl K) := by
  obtain ⟨φ, hφ⟩ := h
  exact ⟨.not φ, fun M x => not_congr (hφ M x)⟩

/-- Compactness step in Blue Book Thm. 2.76 (2010 fourth corrected printing,
p. 109). If a class and its complement are each defined by theories, a finite
conjunction from the first theory defines the class. Uses first-order compactness
through the modal inconsistency bridge, retaining empty conjunctions/classes. -/
theorem definableByFormula_of_class_and_compl_definable
    {Atom : Type} {K : PointedModelClass.{0, v} Atom}
    (hK : K.IsModallyDefinable) (hC : IsModallyDefinable (compl K)) :
    K.IsDefinableByFormula := by
  classical
  obtain ⟨T₁, h₁⟩ := hK
  obtain ⟨T₂, h₂⟩ := hC
  have hn : ¬ ∃ (W : Type v) (M : Unimodal.Model W Atom) (x : W),
      ∀ φ ∈ T₁ ∪ T₂, Satisfies M x φ := by
    rintro ⟨W, M, x, hx⟩
    exact (h₂ M x).mpr (fun φ hφ => hx φ (Or.inr hφ))
      ((h₁ M x).mpr (fun φ hφ => hx φ (Or.inl hφ)))
  obtain ⟨Δ, hΔ, hnΔ⟩ := exists_finite_unsatisfiable_of_unsatisfiable (T₁ ∪ T₂) hn
  let Φ := Δ.filter (· ∈ T₁)
  refine ⟨Cslib.Logic.finiteAnd Φ.toList, ?_⟩
  intro W M x
  let : Nonempty W := ⟨x⟩
  constructor
  · intro hx
    apply Satisfies.finiteAnd_iff_forall.mpr
    intro φ hφ
    exact (h₁ M x).mp hx φ (Finset.mem_filter.mp (Finset.mem_toList.mp hφ)).2
  · intro hx
    by_contra hnot
    have ht₂ := (h₂ M x).mp hnot
    apply hnΔ
    refine ⟨W, M, x, ?_⟩
    intro φ hφ
    rcases hΔ φ hφ with hφ₁ | hφ₂
    · exact Satisfies.finiteAnd_iff_forall.mp hx φ
        (Finset.mem_toList.mpr (Finset.mem_filter.mpr ⟨hφ, hφ₁⟩))
    · exact ht₂ φ hφ₂

/-- CONDITIONAL Blue Book Thm. 2.76 (2010 fourth corrected printing, p. 109),
basic unimodal models at fixed arbitrary world universe. The forward direction
of Thm. 2.74 remains an explicit premise of this helper, exactly as for conditional
Thm. 2.75. The proof applies 2.75 to the class and complement, then compactness;
this is NOT an unconditional proof of 2.76. Lemma 2.73 is proved separately. -/
theorem definableByFormula_iff_of_bisimilar_ultrapowers
    {Atom : Type}
    (h274 : ∀ {W W' : Type v} (M : Unimodal.Model W Atom)
      (N : Unimodal.Model W' Atom) [Nonempty W] [Nonempty W'] (x : W) (y : W'),
      ModallyEquivalent M N x y → ∃ (I : Type) (U : Ultrafilter I),
        ModallyBisimilar (modalUltrapower M U) (modalUltrapower N U)
          ((fun _ : I => x) : (U : Filter I).Product (fun _ : I => W))
          ((fun _ : I => y) : (U : Filter I).Product (fun _ : I => W')))
    (K : PointedModelClass.{0, v} Atom) :
    K.IsDefinableByFormula ↔
      (K.ClosedUnderBisimulations ∧ K.ClosedUnderUltraproducts) ∧
      (ClosedUnderBisimulations (compl K) ∧ ClosedUnderUltraproducts (compl K)) := by
  constructor
  · intro h
    exact ⟨⟨h.isModallyDefinable.closedUnderBisimulations,
      h.isModallyDefinable.closedUnderUltraproducts⟩,
      ⟨h.compl.isModallyDefinable.closedUnderBisimulations,
        h.compl.isModallyDefinable.closedUnderUltraproducts⟩⟩
  · rintro ⟨⟨hB, hU⟩, ⟨hCB, hCU⟩⟩
    have hK := (modallyDefinable_iff_of_bisimilar_ultrapowers h274 K).mpr
      ⟨hB, hU, fun M _ U x hx => hCU (fun _ => M) U (fun _ => x) (fun _ => hx)⟩
    have hC := (modallyDefinable_iff_of_bisimilar_ultrapowers h274 (compl K)).mpr
      ⟨hCB, hCU, ?_⟩
    · exact definableByFormula_of_class_and_compl_definable hK hC
    · intro I W M _ U x hx
      change ¬ ¬ K M x at hx
      change ¬ ¬ K (modalUltrapower M U) _
      exact not_not.mpr (hU (fun _ : I => M) U (fun _ => x) (fun _ => not_not.mp hx))

/-- Blue Book Thm. 2.75 (2010 fourth corrected printing, pp. 107–109),
for basic unimodal logic with countable `Atom : Type`. The pointed class ranges
over all carriers at arbitrary fixed universe `v`; worlds are not assumed
countable. Theory definability is equivalent to bisimulation and ultraproduct
closure of the class and ultrapower closure of its complement. Supplies the
forward direction of the proved Thm. 2.74 to the general composition above;
no saturation or Thm. 2.74 premise remains in this declaration. -/
theorem modallyDefinable_iff {Atom : Type} [Countable Atom]
    (K : PointedModelClass.{0, v} Atom) :
    K.IsModallyDefinable ↔ K.ClosedUnderBisimulations ∧ K.ClosedUnderUltraproducts ∧
      ClosedUnderUltrapowers (compl K) := by
  apply modallyDefinable_iff_of_bisimilar_ultrapowers
  intro W W' M N _ _ x y h
  exact (modallyEquivalent_iff_exists_bisimilar_ultrapowers M N x y).mp h

/-- Blue Book Thm. 2.76 (2010 fourth corrected printing, p. 109), for basic
unimodal logic with countable `Atom : Type` and pointed classes at arbitrary
fixed world universe `v`. Single-formula definability is equivalent to closure
of both the class and its complement under bisimulations and ultraproducts.
Uses the proved Thm. 2.74, the Thm. 2.75 composition and compactness; no extra
unproved premise is assumed. This concerns model classes, not frame classes. -/
theorem definableByFormula_iff {Atom : Type} [Countable Atom]
    (K : PointedModelClass.{0, v} Atom) :
    K.IsDefinableByFormula ↔
      (K.ClosedUnderBisimulations ∧ K.ClosedUnderUltraproducts) ∧
      (ClosedUnderBisimulations (compl K) ∧ ClosedUnderUltraproducts (compl K)) := by
  apply definableByFormula_iff_of_bisimilar_ultrapowers
  intro W W' M N _ _ x y h
  exact (modallyEquivalent_iff_exists_bisimilar_ultrapowers M N x y).mp h

end ModalCharacterization.PointedModelClass
