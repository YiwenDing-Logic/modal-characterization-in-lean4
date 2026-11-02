/- Modal Characterization in Lean. Released under Apache-2.0; see LICENSE. -/
module

public import ModalCharacterization.Modal.ModelClass

@[expose] public section

namespace ModalCharacterization
open Cslib.Logic.Modal
universe u v z

/-- Implementation transport for Blue Book Thm. 2.75 (2010 fourth corrected
printing, pp. 107–109): lifting the index universe does not change the pointed
ultraproduct up to bisimulation. This auxiliary lemma is not separately numbered
in the book. The proof reindexes representatives and transports the ultrafilter
by `Ultrafilter.map`; it does not use saturation or modal equivalence alone. -/
theorem modalUltraproduct_ulift_bisimilar
    {Atom : Type u} {I : Type z} {W : I → Type v}
    (M : ∀ i, Unimodal.Model (W i) Atom) [∀ i, Nonempty (W i)]
    (U : Ultrafilter I) (x : ∀ i, W i) :
    ModallyBisimilar
      (modalUltraproduct (fun i : ULift.{v} I => M i.down) (U.map ULift.up))
      (modalUltraproduct M U)
      ((fun i : ULift.{v} I => x i.down) :
        ((U.map ULift.up : Ultrafilter (ULift.{v} I)) : Filter _).Product
          (fun i : ULift.{v} I => W i.down))
      (x : (U : Filter I).Product W) := by
  let V : Ultrafilter (ULift.{v} I) := U.map ULift.up
  let e : (V : Filter _).Product (fun i : ULift.{v} I => W i.down) ≃ (U : Filter I).Product W :=
    { toFun := Quotient.map (fun f i => f (ULift.up i)) (by
        intro f g h
        exact h)
      invFun := Quotient.map (fun f (i : ULift.{v} I) => f i.down) (by
        intro f g h
        exact h)
      left_inv := by intro a; induction a using Quotient.inductionOn with | h f => rfl
      right_inv := by intro a; induction a using Quotient.inductionOn with | h f => rfl }
  have ha : ∀ a p,
      (modalUltraproduct (fun i : ULift.{v} I => M i.down) V).v a p ↔
        (modalUltraproduct M U).v (e a) p := by
    intro a p
    induction a using Quotient.inductionOn with
    | h f => rfl
  have hr : ∀ a b,
      (modalUltraproduct (fun i : ULift.{v} I => M i.down) V).toFrame.rel a b ↔
        (modalUltraproduct M U).toFrame.rel (e a) (e b) := by
    intro a b
    induction a using Quotient.inductionOn with
    | h f =>
      induction b using Quotient.inductionOn with
      | h g => rfl
  refine ⟨fun a b => e a = b, ?_, rfl⟩
  apply (isModalBisimulation_iff _ _ _).mpr
  refine ⟨⟨((fun i : ULift.{v} I => x i.down) :
    (V : Filter _).Product (fun i : ULift.{v} I => W i.down)), _, rfl⟩, ?_, ?_, ?_⟩
  · intro a b hab p
    subst b
    exact ha a p
  · intro a b hab a' haa'
    subst b
    exact ⟨e a', (hr a a').mp haa', rfl⟩
  · intro a b hab b' hbb'
    subst b
    refine ⟨e.symm b', ?_, e.apply_symm_apply b'⟩
    apply (hr a (e.symm b')).mpr
    simpa using hbb'

namespace PointedModelClass

/-- Auxiliary small-index form of the ultraproduct closure preceding Blue Book
Thm. 2.75 (2010 printing, p. 107). Bisimulation closure transports membership
back from a lifted index type; component carriers remain arbitrary `Type v`. -/
theorem ClosedUnderUltraproducts.smallIndex
    {Atom : Type u} {K : PointedModelClass.{u, v} Atom}
    (hU : K.ClosedUnderUltraproducts) (hB : K.ClosedUnderBisimulations)
    {I : Type} {W : I → Type v} (M : ∀ i, Unimodal.Model (W i) Atom)
    [∀ i, Nonempty (W i)] (U : Ultrafilter I) (x : ∀ i, W i)
    (hx : ∀ i, K (M i) (x i)) :
    K (modalUltraproduct M U) (x : (U : Filter I).Product W) := by
  exact hB _ _ _ _
    (hU (fun i : ULift.{v} I => M i.down) (U.map ULift.up)
      (fun i => x i.down) (fun i => hx i.down))
    (modalUltraproduct_ulift_bisimilar M U x)

/-- Auxiliary small-index form of pointed ultrapower closure for Blue Book
Thm. 2.75 (2010 printing, pp. 107–109), enabling the natural-number-indexed
ultrapowers used by Thm. 2.74. Uses actual bisimilarity under index lifting. -/
theorem ClosedUnderUltrapowers.smallIndex
    {Atom : Type u} {K : PointedModelClass.{u, v} Atom}
    (hU : K.ClosedUnderUltrapowers) (hB : K.ClosedUnderBisimulations)
    {I : Type} {W : Type v} (M : Unimodal.Model W Atom) [Nonempty W]
    (U : Ultrafilter I) (x : W) (hx : K M x) :
    K (modalUltrapower M U)
      ((fun _ : I => x) : (U : Filter I).Product (fun _ : I => W)) := by
  exact hB _ _ _ _ (hU M (U.map (ULift.up : I → ULift.{v} I)) x hx)
    (modalUltraproduct_ulift_bisimilar (fun _ : I => M) U (fun _ => x))

end PointedModelClass
end ModalCharacterization
