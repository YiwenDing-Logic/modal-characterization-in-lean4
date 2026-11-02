/- Modal Characterization in Lean 4. Released under Apache-2.0; see LICENSE. -/
module

public import ModalCharacterization.Modal.UltraproductReindex
public import Mathlib.Order.Filter.Ultrafilter.Basic

@[expose] public section

namespace ModalCharacterization.PointedModelClass
open Cslib.Logic.Modal
universe v

/-- Blue Book Thm. 2.75, Claim 1 (2010 fourth corrected printing, p. 108),
basic unimodal specialization: finite satisfiability in a pointed class yields
realization in an ultraproduct of members of that class. Atoms lie in `Type`,
component worlds in arbitrary `Type v`; neither is required to be countable.
The proof follows finite-subset indices, the finite intersection property,
ultrafilter extension (Fact A.14), and Łoś (Thm. A.19 via standard translation).
The resulting ultraproduct is not asserted to belong to the class. -/
theorem exists_ultraproduct_realizing
    {Atom : Type} {K : PointedModelClass.{0, v} Atom}
    (Γ : Set (Unimodal.Proposition Atom))
    (hfin : ∀ Δ : Finset (Unimodal.Proposition Atom),
      (∀ φ ∈ Δ, φ ∈ Γ) → ∃ (W : Type v) (M : Unimodal.Model W Atom) (x : W),
        K M x ∧ ∀ φ ∈ Δ, Satisfies M x φ) :
    ∃ (I : Type) (U : Ultrafilter I) (W : I → Type v)
      (_hW : ∀ i, Nonempty (W i)) (M : ∀ i, Unimodal.Model (W i) Atom) (x : ∀ i, W i),
      (∀ i, K (M i) (x i)) ∧
        ∀ φ ∈ Γ, Satisfies (modalUltraproduct M U) (x : (U : Filter I).Product W) φ := by
  classical
  let I := Finset Γ
  have hm : ∀ Δ : I, ∃ (W : Type v) (M : Unimodal.Model W Atom) (x : W),
      K M x ∧ ∀ φ ∈ Δ, Satisfies M x φ.val := by
    intro Δ
    obtain ⟨W, M, x, hx, hΔ⟩ := hfin (Δ.image Subtype.val) (by
      intro φ hφ
      obtain ⟨ψ, _, rfl⟩ := Finset.mem_image.mp hφ
      exact ψ.property)
    exact ⟨W, M, x, hx, fun φ hφ => hΔ φ.val (Finset.mem_image.mpr ⟨φ, hφ, rfl⟩)⟩
  choose W M x hK hx using hm
  let cone (φ : Γ) : Set I := {Δ | φ ∈ Δ}
  have hFIP : ∀ T : Finset (Set I), (↑T : Set (Set I)) ⊆ Set.range cone →
      (⋂₀ (↑T : Set (Set I))).Nonempty := by
    intro T hT
    have haux : ∃ Δ : I, ∀ φ : Γ, cone φ ∈ T → φ ∈ Δ := by
      induction T using Finset.induction_on with
      | empty => exact ⟨∅, by simp⟩
      | @insert s T hs ih =>
        obtain ⟨φ, rfl⟩ := hT (Finset.mem_insert_self s T)
        obtain ⟨Δ, hΔ⟩ := ih (fun t ht => hT (Finset.mem_insert_of_mem ht))
        refine ⟨insert φ Δ, ?_⟩
        intro ψ hψ
        rcases Finset.mem_insert.mp hψ with heq | hmem
        · have hψ' : ψ ∈ ({φ} : Finset Γ) := by
            change ({φ} : I) ∈ cone ψ
            rw [heq]
            exact Finset.mem_singleton_self φ
          have : ψ = φ := Finset.mem_singleton.mp hψ'
          subst ψ
          exact Finset.mem_insert_self _ _
        · exact Finset.mem_insert_of_mem (hΔ ψ hmem)
    obtain ⟨Δ, hΔ⟩ := haux
    refine ⟨Δ, ?_⟩
    intro s hs
    obtain ⟨φ, rfl⟩ := hT hs
    exact hΔ φ hs
  obtain ⟨U, hU⟩ := Ultrafilter.exists_ultrafilter_of_finite_inter_nonempty
    (Set.range cone) hFIP
  let : ∀ i, Nonempty (W i) := fun i => ⟨x i⟩
  refine ⟨I, U, W, inferInstance, M, x, hK, ?_⟩
  intro φ hφ
  apply (satisfies_modalUltraproduct M U φ x).mpr
  exact Filter.mem_of_superset (hU (Set.mem_range_self (⟨φ, hφ⟩ : Γ)))
    (fun Δ hΔ => hx Δ ⟨φ, hφ⟩ hΔ)

/-- Application of Claim 1 in Blue Book Thm. 2.75
(2010 fourth corrected printing, p. 108): a finitely satisfiable formula set
has a realization inside a bisimulation- and ultraproduct-closed pointed class.
Bisimulation closure is used solely for the explicit small-index transport.
This does not use the later invocation of Thm. 2.74 or Lemma 2.73. -/
theorem exists_realization_of_finitely_satisfiable
    {Atom : Type} {K : PointedModelClass.{0, v} Atom}
    (hU : K.ClosedUnderUltraproducts) (hB : K.ClosedUnderBisimulations)
    (Γ : Set (Unimodal.Proposition Atom))
    (hfin : ∀ Δ : Finset (Unimodal.Proposition Atom),
      (∀ φ ∈ Δ, φ ∈ Γ) → ∃ (W : Type v) (M : Unimodal.Model W Atom) (x : W),
        K M x ∧ ∀ φ ∈ Δ, Satisfies M x φ) :
    ∃ (W : Type v) (M : Unimodal.Model W Atom) (x : W),
      K M x ∧ ∀ φ ∈ Γ, Satisfies M x φ := by
  obtain ⟨I, U, W, hW, M, x, hK, hΓ⟩ := exists_ultraproduct_realizing Γ hfin
  let : ∀ i, Nonempty (W i) := hW
  exact ⟨(U : Filter I).Product W, modalUltraproduct M U, _,
    hU.smallIndex hB M U x hK, hΓ⟩

/-- Finite-satisfiability step preceding Claim 1 in Blue Book Thm. 2.75
(2010 fourth corrected printing, p. 108), basic unimodal specialization.
A point satisfying every modal formula true throughout `K` has its full modal
theory finitely satisfiable in `K`. The proof uses the negation of a finite
conjunction, including the empty conjunction. No closure assumption is needed. -/
theorem theory_finitely_satisfiable_of_modal_consequences
    {Atom : Type*} {K : PointedModelClass.{_, v} Atom}
    {W : Type v} (M : Unimodal.Model W Atom) (x : W)
    (h : ∀ φ : Unimodal.Proposition Atom,
      (∀ {V : Type v} (N : Unimodal.Model V Atom) (y : V), K N y → Satisfies N y φ) →
        Satisfies M x φ) :
    ∀ Δ : Finset (Unimodal.Proposition Atom),
      (∀ φ ∈ Δ, φ ∈ theory M x) →
        ∃ (V : Type v) (N : Unimodal.Model V Atom) (y : V),
          K N y ∧ ∀ φ ∈ Δ, Satisfies N y φ := by
  classical
  let : Nonempty W := ⟨x⟩
  intro Δ hΔ
  by_contra hn
  have hneg : Satisfies M x (.not (Cslib.Logic.finiteAnd Δ.toList)) := by
    apply h
    intro V N y hy
    let : Nonempty V := ⟨y⟩
    intro hc
    apply hn
    refine ⟨V, N, y, hy, ?_⟩
    intro φ hφ
    exact (Satisfies.finiteAnd_iff_forall.mp hc) φ (Finset.mem_toList.mpr hφ)
  apply hneg
  apply Satisfies.finiteAnd_iff_forall.mpr
  intro φ hφ
  exact hΔ φ (Finset.mem_toList.mp hφ)

/-- Consequence of Claim 1 in Blue Book Thm. 2.75
(2010 fourth corrected printing, p. 108), before the invocation of Thm. 2.74:
a point satisfying all modal consequences of a bisimulation- and ultraproduct-
closed class has a modally equivalent point in that class. Full theory inclusion
gives equality using negation. Atoms lie in `Type`; worlds may have any universe.
No saturation or countability assumption, and no assertion of membership of the
original point. -/
theorem exists_modallyEquivalent_of_modal_consequences
    {Atom : Type} {K : PointedModelClass.{0, v} Atom}
    (hU : K.ClosedUnderUltraproducts) (hB : K.ClosedUnderBisimulations)
    {W : Type v} (M : Unimodal.Model W Atom) (x : W)
    (h : ∀ φ : Unimodal.Proposition Atom,
      (∀ {V : Type v} (N : Unimodal.Model V Atom) (y : V), K N y → Satisfies N y φ) →
        Satisfies M x φ) :
    ∃ (V : Type v) (N : Unimodal.Model V Atom) (y : V),
      K N y ∧ ModallyEquivalent M N x y := by
  obtain ⟨V, N, y, hy, ht⟩ := exists_realization_of_finitely_satisfiable hU hB
    (theory M x) (theory_finitely_satisfiable_of_modal_consequences M x h)
  let : Nonempty W := ⟨x⟩
  let : Nonempty V := ⟨y⟩
  exact ⟨V, N, y, hy, modallyEquivalent_of_theory_subset (fun φ hφ => ht φ hφ)⟩

end ModalCharacterization.PointedModelClass
