/-
Modal Characterization in Lean 4. Released under Apache-2.0; see LICENSE.
Blue Book, 2010 fourth corrected printing, §2.5.
Reuses mathlib ultrafilters and CSLib frames/models. Prior work includes
Mashu Noguchi's complex algebras and Xu/Norrish's HOL4 ultrafilter extensions.
No Foundation/ModalLogic or HOL4 code is copied or imported.
-/
module

public import ModalCharacterization.Ultrafilter.Relation
public import Cslib.Logics.Modal.Unimodal.Basic
public import ModalCharacterization.Modal.Saturation

@[expose] public section

namespace ModalCharacterization

open Cslib.Logic.Modal

universe u v
variable {W : Type v} {Atom : Type u}

/-- Frame component of Blue Book Def. 2.57 (2010 printing, p. 94), for a
single unary modality. It depends only on the original frame, not a valuation.
The diamond-based relation is kept explicit; the relation toolkit supplies
its equivalent box form. No cardinality restriction is imposed on worlds. -/
def ultrafilterFrame {τ : PFunctor} [PFunctor.Unary τ] [Unique τ.A]
    (F : Cslib.Frame W τ) : Cslib.Frame (Ultrafilter W) τ :=
  Cslib.Frame.ofRelation fun a b =>
    ∀ X ∈ b, ({w | ∃ z ∈ X, F.rel w z} : Set W) ∈ a

/-- Blue Book Def. 2.57 (2010 printing, p. 94), basic unimodal model extension.
Atomic truth at an ultrafilter means membership of the original atomic truth set.
For nonempty original worlds, principal ultrafilters ensure nonempty new worlds. -/
def ultrafilterExtension (M : Unimodal.Model W Atom) :
    Unimodal.Model (Ultrafilter W) Atom where
  toFrame := ultrafilterFrame M.toFrame
  v := fun a p => {w | M.v w p} ∈ a

/-- Implementation bridge for Def. 2.57: the explicitly stated diamond relation
is mathlib's relation lifting. Auxiliary, not a separate book proposition. -/
theorem ultrafilterFrame_rel_iff {τ : PFunctor} [PFunctor.Unary τ] [Unique τ.A]
    (F : Cslib.Frame W τ) (a b : Ultrafilter W) :
    (ultrafilterFrame F).rel a b ↔
      Filter.RTendsto' ({p | F.rel p.1 p.2} : SetRel W W) a b :=
  (UltrafilterRelation.rtendsto'_iff_diamond
    ({p | F.rel p.1 p.2} : SetRel W W) a b).symm

/-- Blue Book equation (2.1) (2010 printing, p. 95), basic unimodal frame
specialization. Principal points preserve and reflect accessibility; no bounded
morphism or first-order elementarity is asserted. -/
theorem ultrafilterFrame_rel_pure_iff {τ : PFunctor} [PFunctor.Unary τ] [Unique τ.A]
    (F : Cslib.Frame W τ) (x y : W) :
    (ultrafilterFrame F).rel (pure x) (pure y) ↔ F.rel x y := by
  rw [ultrafilterFrame_rel_iff]
  exact UltrafilterRelation.rtendsto'_pure_iff _ x y

/-- Auxiliary principal-point atom check for Blue Book Prop. 2.59(ii)
(2010 printing, pp. 96–97). The full formula theorem remains separate. -/
theorem ultrafilterExtension_atom_pure (M : Unimodal.Model W Atom) (x : W)
    (p : Atom) : (ultrafilterExtension M).v (pure x) p ↔ M.v x p := Iff.rfl

/-- Auxiliary successor existence for the diamond case of Blue Book Prop. 2.59(i)
(2010 printing, pp. 96–97). It applies to every subset `X`, not just truth sets,
and uses the book's box-family extension argument via the generic filter lemma. -/
theorem ultrafilterFrame_exists_successor_mem {τ : PFunctor}
    [PFunctor.Unary τ] [Unique τ.A] (F : Cslib.Frame W τ)
    (a : Ultrafilter W) (X : Set W)
    (hX : ({w | ∃ z ∈ X, F.rel w z} : Set W) ∈ a) :
    ∃ b : Ultrafilter W, (ultrafilterFrame F).rel a b ∧ X ∈ b := by
  obtain ⟨b, hb, hmem⟩ := UltrafilterRelation.exists_successor_mem
    ({p | F.rel p.1 p.2} : SetRel W W) a X hX
  exact ⟨b, (ultrafilterFrame_rel_iff F a b).mpr hb, hmem⟩

/-- Blue Book Prop. 2.59(i) (2010 fourth corrected printing, pp. 96–97),
basic unimodal truth lemma. No restrictions on the cardinalities of atoms or
worlds. The proof follows formula induction; the diamond existence direction
uses the box-family ultrafilter extension established above. -/
theorem ultrafilterExtension_truth (M : Unimodal.Model W Atom)
    (φ : Unimodal.Proposition Atom) (a : Ultrafilter W) :
    {w | Satisfies M w φ} ∈ a ↔ Satisfies (ultrafilterExtension M) a φ := by
  classical
  induction φ generalizing a with
  | atom p => rfl
  | false => exact iff_false_intro Ultrafilter.empty_notMem
  | not ψ ih =>
    change ({w | Satisfies M w ψ}ᶜ ∈ a) ↔ ¬Satisfies (ultrafilterExtension M) a ψ
    rw [Ultrafilter.compl_mem_iff_notMem, ih]
  | or ψ χ ihψ ihχ =>
    change ({w | Satisfies M w ψ} ∪ {w | Satisfies M w χ}) ∈ a ↔ _
    rw [Ultrafilter.union_mem_iff, ihψ, ihχ]
    rfl
  | triangle op ψs ih =>
    have heq : Proposition.triangle op ψs =
        Cslib.Logic.HasDiamond.diamond (ψs default) := by
      cases op
      exact Proposition.unary_triangle_eq_dynDiamond ψs
    have hset : {w | Satisfies M w (Proposition.triangle op ψs)} =
        {w | ∃ z ∈ {z | Satisfies M z (ψs default)}, M.toFrame.rel w z} := by
      ext w
      rw [heq]
      have hm : Satisfies M w (Cslib.Logic.HasDiamond.diamond (ψs default)) ↔
          ∃ z, M.toFrame.rel w z ∧ Satisfies M z (ψs default) :=
        Satisfies.diamond_iff_exists
      exact hm.trans (by simp only [Set.mem_ofPred_eq, and_comm])
    have hn : Satisfies (ultrafilterExtension M) a
        (Cslib.Logic.HasDiamond.diamond (ψs default)) ↔
        ∃ b, (ultrafilterExtension M).toFrame.rel a b ∧
          Satisfies (ultrafilterExtension M) b (ψs default) :=
      Satisfies.diamond_iff_exists
    rw [hset, heq, hn]
    constructor
    · intro h
      obtain ⟨b, hab, hb⟩ := ultrafilterFrame_exists_successor_mem M.toFrame a _ h
      exact ⟨b, hab, (ih default b).mp hb⟩
    · rintro ⟨b, hab, hb⟩
      exact hab _ ((ih default b).mpr hb)

/-- Blue Book Prop. 2.59(ii) (2010 fourth corrected printing, pp. 96–97):
a world and its principal ultrafilter agree on every basic modal formula.
This is modal equivalence, not first-order equivalence or a bounded morphism. -/
theorem modallyEquivalent_ultrafilterExtension_pure (M : Unimodal.Model W Atom)
    (x : W) : ModallyEquivalent M (ultrafilterExtension M) x (pure x) := by
  apply modallyEquivalent_iff.mpr
  intro φ
  exact ultrafilterExtension_truth M φ (pure x)

/-- Blue Book Prop. 2.61 (2010 fourth corrected printing, p. 97), basic
unimodal specialization. Every ultrafilter extension is modally saturated.
The proof extends the box-family together with the truth sets of the type.
Finite intersections of truth sets represent the book's finite conjunctions;
finite satisfiability supplies a successor ultrafilter witnessing each finite
intersection. No restriction on type, atom or world cardinalities is imposed. -/
theorem ultrafilterExtension_isModallySaturated (M : Unimodal.Model W Atom) :
    IsModallySaturated (ultrafilterExtension M) := by
  classical
  intro a Γ hfin
  let R : SetRel W W := {p | M.toFrame.rel p.1 p.2}
  let B : Set (Set W) := {X | R.core X ∈ a}
  let A : Set (Set W) := B ∪ (fun φ => {w | Satisfies M w φ}) '' Γ
  have hbox (b : Ultrafilter W)
      (hab : (ultrafilterExtension M).toFrame.rel a b) : ∀ X ∈ B, X ∈ b := by
    exact (UltrafilterRelation.rtendsto'_iff_box R a b).mp
      ((ultrafilterFrame_rel_iff M.toFrame a b).mp hab)
  have hfinite : ∀ T : Finset (Set W), (↑T : Set (Set W)) ⊆ A →
      ∃ Δ : Finset (Unimodal.Proposition Atom), (∀ φ ∈ Δ, φ ∈ Γ) ∧
        ∀ b : Ultrafilter W, (ultrafilterExtension M).toFrame.rel a b →
          (∀ φ ∈ Δ, Satisfies (ultrafilterExtension M) b φ) →
          ∀ X ∈ T, X ∈ b := by
    intro T
    induction T using Finset.induction_on with
    | empty => exact fun _ => ⟨∅, by simp, by simp⟩
    | @insert X T hn ih =>
      intro hT
      obtain ⟨Δ, hΔ, hw⟩ := ih (fun Y hY => hT (Finset.mem_insert_of_mem hY))
      rcases hT (Finset.mem_insert_self X T) with hX | ⟨φ, hφ, rfl⟩
      · refine ⟨Δ, hΔ, ?_⟩
        intro b hab hb Y hY
        rcases Finset.mem_insert.mp hY with rfl | hY
        · exact hbox b hab _ hX
        · exact hw b hab hb Y hY
      · refine ⟨insert φ Δ, ?_, ?_⟩
        · intro ψ hψ
          rcases Finset.mem_insert.mp hψ with rfl | hψ
          · exact hφ
          · exact hΔ ψ hψ
        · intro b hab hb Y hY
          rcases Finset.mem_insert.mp hY with rfl | hY
          · exact (ultrafilterExtension_truth M φ b).mpr (hb φ (Finset.mem_insert_self _ _))
          · exact hw b hab (fun ψ hψ => hb ψ (Finset.mem_insert_of_mem hψ)) Y hY
  have hFIP : ∀ T : Finset (Set W), (↑T : Set (Set W)) ⊆ A →
      (⋂₀ (↑T : Set (Set W))).Nonempty := by
    intro T hT
    obtain ⟨Δ, hΔ, hw⟩ := hfinite T hT
    obtain ⟨b, hab, hb⟩ := hfin Δ hΔ
    exact b.nonempty_of_mem ((Filter.sInter_mem T.finite_toSet).mpr (hw b hab hb))
  obtain ⟨b, hb⟩ := Ultrafilter.exists_ultrafilter_of_finite_inter_nonempty A hFIP
  refine ⟨b, ?_, ?_⟩
  · apply (ultrafilterFrame_rel_iff M.toFrame a b).mpr
    apply (UltrafilterRelation.rtendsto'_iff_box R a b).mpr
    intro X hX
    exact hb (Or.inl hX)
  · intro φ hφ
    exact (ultrafilterExtension_truth M φ b).mp (hb (Or.inr ⟨φ, hφ, rfl⟩))

/-- Blue Book Thm. 2.62 (2010 fourth corrected printing, p. 98), basic
unimodal pointed models: modal equivalence is exactly bisimilarity of principal
points in their ultrafilter extensions. Combines Prop. 2.59, Prop. 2.61 and the
saturated Hennessy–Milner theorem (Prop. 2.54), following the book.
World carriers may have different universes; no countability premise is needed. -/
theorem modallyEquivalent_iff_ultrafilterExtension_bisimilar
    {W' : Type*} (M : Unimodal.Model W Atom) (N : Unimodal.Model W' Atom)
    (x : W) (y : W') :
    ModallyEquivalent M N x y ↔
      ModallyBisimilar (ultrafilterExtension M) (ultrafilterExtension N)
        (pure x) (pure y) := by
  let : Nonempty (Ultrafilter W) := ⟨pure x⟩
  let : Nonempty (Ultrafilter W') := ⟨pure y⟩
  have hx := modallyEquivalent_ultrafilterExtension_pure M x
  have hy := modallyEquivalent_ultrafilterExtension_pure N y
  rw [← (ultrafilterExtension_isModallySaturated M).modallyEquivalent_iff_bisimilar
    (ultrafilterExtension_isModallySaturated N)]
  exact ⟨fun h => hx.symm.trans (h.trans hy), fun h => hx.trans (h.trans hy.symm)⟩

end ModalCharacterization
