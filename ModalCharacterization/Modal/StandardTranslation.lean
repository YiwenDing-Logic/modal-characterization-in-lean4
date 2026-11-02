/-
Modal Characterization in Lean. Released under Apache-2.0; see LICENSE.
Uses mathlib and, in the modal adapter, CSLib (Fabrizio Montesi, Marianna Girlando).
Blue Book: Blackburn, de Rijke, Venema, Modal Logic, fourth printing (2010).
Foundation's historical standard translation by Mashu Noguchi is prior work;
no Foundation code is copied, ported or imported here.
-/
module

public import ModalCharacterization.Modal.ModelBridge
public import ModalCharacterization.Modal.Bisimulation

/-! Binder bookkeeping supplies implementation details for the structural induction in
Blue Book Prop. 2.47 (2010, p. 85; Exercise 2.4.1). The helpers below are not separately
numbered book propositions. Bound indices encode scopes rather than variable names. -/

@[expose] public section

namespace ModalCharacterization

universe u v
variable {Atom : Type u} {W : Type v}

/-- Implementation helper for Blue Book Def. 2.45 / Prop. 2.47(i) (2010, pp. 84–85).
Keep the free variable and old bound variables when appending a fresh binder. -/
def underBinder {n : Nat} (i : Fin 1 ⊕ Fin n) : Fin 1 ⊕ Fin (n + 1) :=
  Sum.map id Fin.castSucc i

/-- Implementation helper for Blue Book Def. 2.45 / Prop. 2.47(i) (2010, pp. 84–85).
Appending a witness preserves the interpretation of the previous current world. -/
theorem underBinder_realize {n : Nat} (i : Fin 1 ⊕ Fin n)
    (v : Fin 1 → W) (xs : Fin n → W) (z : W) :
    Sum.elim v (Fin.snoc xs z) (underBinder i) = Sum.elim v xs i := by
  cases i <;> simp [underBinder]

/-- Implementation helper for Blue Book Def. 2.45 / Prop. 2.47(i) (2010, pp. 84–85).
The newly appended variable denotes exactly the new witness. -/
theorem fresh_realize {n : Nat} (v : Fin 1 → W) (xs : Fin n → W) (z : W) :
    Sum.elim v (Fin.snoc xs z) (Sum.inr (Fin.last n)) = z := by
  simp

/-- Implementation helper for Blue Book Def. 2.45 / Prop. 2.47(i) (2010, pp. 84–85).
Atomic translation at an arbitrary current-world variable. -/
def atomAt {n : Nat} (i : Fin 1 ⊕ Fin n) (p : Atom) :
    (language Atom).BoundedFormula (Fin 1) n :=
  FirstOrder.Language.Relations.boundedFormula₁ (RelationSymbol.atom p) (.var i)

/-- Implementation helper for Blue Book Def. 2.45 / Prop. 2.47(i) (2010, pp. 84–85).
Existential diamond constructor; its body must be translated at the fresh variable. -/
def diamondAt {n : Nat} (i : Fin 1 ⊕ Fin n)
    (body : (language Atom).BoundedFormula (Fin 1) (n + 1)) :
    (language Atom).BoundedFormula (Fin 1) n :=
  let edge := FirstOrder.Language.Relations.boundedFormula₂ (L := language Atom)
    RelationSymbol.access (.var (underBinder i)) (.var (.inr (Fin.last n)))
  (edge ⊓ body).ex

/-- Implementation helper for Blue Book Def. 2.45 / Prop. 2.47(i) (2010, pp. 84–85).
Bounded formula interpretation with an explicit Kripke model. -/
def boundedHolds (M : Cslib.Logic.Modal.Unimodal.Model W Atom) [Nonempty W]
    {n : Nat} (φ : (language Atom).BoundedFormula (Fin 1) n)
    (v : Fin 1 → W) (xs : Fin n → W) : Prop :=
  letI : (language Atom).Structure W := toStructure M
  φ.Realize v xs

/-- Atomic semantic helper for the induction in Blue Book Prop. 2.47(i) (2010, p. 85). -/
theorem atomAt_realize (M : Cslib.Logic.Modal.Unimodal.Model W Atom) [Nonempty W]
    {n : Nat} (i : Fin 1 ⊕ Fin n) (p : Atom) (v : Fin 1 → W) (xs : Fin n → W) :
    boundedHolds M (atomAt i p) v xs ↔ M.v (Sum.elim v xs i) p := by
  rfl

/-- Implementation helper for Blue Book Def. 2.45 / Prop. 2.47(i) (2010, pp. 84–85).
The generic binder step, valid for every body and every previous assignment. -/
theorem diamondAt_realize (M : Cslib.Logic.Modal.Unimodal.Model W Atom) [Nonempty W]
    {n : Nat} (i : Fin 1 ⊕ Fin n)
    (body : (language Atom).BoundedFormula (Fin 1) (n + 1))
    (v : Fin 1 → W) (xs : Fin n → W) :
    boundedHolds M (diamondAt i body) v xs ↔
      ∃ z, M.toFrame.rel (Sum.elim v xs i) z ∧
        boundedHolds M body v (Fin.snoc xs z) := by
  simp only [boundedHolds, diamondAt,
    FirstOrder.Language.BoundedFormula.realize_ex,
    FirstOrder.Language.BoundedFormula.realize_inf]
  change (∃ z, M.toFrame.rel (Sum.elim v (Fin.snoc xs z) (underBinder i))
    (Sum.elim v (Fin.snoc xs z) (.inr (Fin.last n))) ∧ _) ↔ _
  simp only [underBinder_realize, fresh_realize]

/-- Binder-aware implementation of Blue Book Def. 2.45 (2010 printing, p. 84),
specialized to basic unimodal logic: translation at the current-world variable under `n` binders.
The single operator and its single child in CSLib's unimodal signature are PUnit-indexed. -/
def translateAt (φ : Cslib.Logic.Modal.Unimodal.Proposition Atom)
    {n : Nat} (i : Fin 1 ⊕ Fin n) : (language Atom).BoundedFormula (Fin 1) n :=
  match φ with
  | .atom p => atomAt i p
  | .false => (FirstOrder.Language.BoundedFormula.equal (.var i) (.var i)).not
  | .not ψ => (translateAt ψ i).not
  | .or ψ χ => translateAt ψ i ⊔ translateAt χ i
  | .triangle _ ψs => diamondAt i (translateAt (ψs default) (.inr (Fin.last n)))

/-- Auxiliary induction invariant for Blue Book Prop. 2.47(i) (2010 printing, p. 85).
Quantifies over every current variable and assignment to support the structural induction
specified in the book (Exercise 2.4.1); this is not a separately numbered book proposition. -/
theorem translateAt_correct
    (M : Cslib.Logic.Modal.Unimodal.Model W Atom) [Nonempty W]
    (φ : Cslib.Logic.Modal.Unimodal.Proposition Atom)
    {n : Nat} (i : Fin 1 ⊕ Fin n) (v : Fin 1 → W) (xs : Fin n → W) :
    boundedHolds M (translateAt φ i) v xs ↔
      Cslib.Logic.Modal.Satisfies M (Sum.elim v xs i) φ := by
  induction φ generalizing n v with
  | atom p => exact atomAt_realize M i p v xs
  | false =>
      change (¬ Sum.elim v xs i = Sum.elim v xs i) ↔ False
      exact iff_false_intro (fun h => h rfl)
  | not ψ ih =>
      change (¬ boundedHolds M (translateAt ψ i) v xs) ↔
        ¬ Cslib.Logic.Modal.Satisfies M (Sum.elim v xs i) ψ
      exact not_congr (ih i v xs)
  | or ψ χ ihψ ihχ =>
      change boundedHolds M (translateAt ψ i ⊔ translateAt χ i) v xs ↔
        (Cslib.Logic.Modal.Satisfies M (Sum.elim v xs i) ψ ∨
         Cslib.Logic.Modal.Satisfies M (Sum.elim v xs i) χ)
      have hs (a b : (language Atom).BoundedFormula (Fin 1) n) :
          boundedHolds M (a ⊔ b) v xs ↔
            boundedHolds M a v xs ∨ boundedHolds M b v xs := by
        simp only [boundedHolds, FirstOrder.Language.BoundedFormula.realize_sup]
      exact (hs _ _).trans (or_congr (ihψ i v xs) (ihχ i v xs))
  | triangle op ψs ih =>
      change boundedHolds M
        (diamondAt i (translateAt (ψs default) (.inr (Fin.last n)))) v xs ↔ _
      rw [diamondAt_realize]
      have hmodal : Cslib.Logic.Modal.Satisfies M (Sum.elim v xs i)
          (.triangle op ψs) ↔ ∃ z, M.toFrame.rel (Sum.elim v xs i) z ∧
            Cslib.Logic.Modal.Satisfies M z (ψs default) := by
        have heq : Cslib.Logic.Modal.Proposition.triangle op ψs =
            Cslib.Logic.HasDiamond.diamond (ψs default) := by
          cases op
          exact Cslib.Logic.Modal.Proposition.unary_triangle_eq_dynDiamond ψs
        rw [heq]
        exact Cslib.Logic.Modal.Satisfies.diamond_iff_exists
          (m := M) (w := Sum.elim v xs i) (φ := ψs default)
      rw [hmodal]
      apply exists_congr
      intro z
      apply and_congr_right
      intro _
      simpa only [fresh_realize] using
        ih default (.inr (Fin.last n)) v (Fin.snoc xs z)

/-- Blue Book Def. 2.45 (2010 printing, p. 84), specialized to basic unimodal logic:
top-level standard translation with one available free variable and no outer binders. -/
def standardTranslation (φ : Cslib.Logic.Modal.Unimodal.Proposition Atom) :
    (language Atom).Formula (Fin 1) := translateAt φ (.inl 0)

/-- Blue Book Prop. 2.47(i), Local Correspondence on Models (2010 printing, p. 85),
specialized to basic unimodal logic over nonempty models.
For every model `M`, modal formula `φ`, and world `w`, modal satisfaction at `w` is equivalent
to first-order satisfaction of its standard translation with the free variable assigned `w`. -/
theorem standardTranslation_correct
    (M : Cslib.Logic.Modal.Unimodal.Model W Atom) [Nonempty W]
    (φ : Cslib.Logic.Modal.Unimodal.Proposition Atom) (w : W) :
    Cslib.Logic.Modal.Satisfies M w φ ↔ holds M (standardTranslation φ) w := by
  exact (translateAt_correct M φ (.inl 0) (fun _ => w) Fin.elim0).symm

/-- Auxiliary corollary of Blue Book Theorem 2.20 and Prop. 2.47(i)
(2010 printing, pp. 67, 85), specialized to basic unimodal nonempty models:
standard translations preserve truth at bisimilar points, including across world types.
This is not the full van Benthem characterization or a separately numbered book result. -/
theorem ModallyBisimilar.standardTranslation_iff
    {W' : Type*} {M : Cslib.Logic.Modal.Unimodal.Model W Atom}
    {N : Cslib.Logic.Modal.Unimodal.Model W' Atom} [Nonempty W] [Nonempty W']
    {x : W} {y : W'} (h : ModallyBisimilar M N x y)
    (φ : Cslib.Logic.Modal.Unimodal.Proposition Atom) :
    holds M (standardTranslation φ) x ↔ holds N (standardTranslation φ) y := by
  exact (standardTranslation_correct M φ x).symm.trans
    ((h.satisfies_iff φ).trans (standardTranslation_correct N φ y))

/-- Semantic form of the derived box clause in Blue Book Def. 2.45
(2010 printing, p. 84), obtained from Prop. 2.47(i) and CSLib's box semantics.
Includes worlds with no successors; this is not a separately numbered book proposition. -/
theorem standardTranslation_box_realize
    (M : Cslib.Logic.Modal.Unimodal.Model W Atom) [Nonempty W]
    (φ : Cslib.Logic.Modal.Unimodal.Proposition Atom) (w : W) :
    holds M (standardTranslation (Cslib.Logic.HasBox.box φ)) w ↔
      ∀ z, M.toFrame.rel w z → holds M (standardTranslation φ) z := by
  rw [← standardTranslation_correct]
  refine (Cslib.Logic.Modal.Satisfies.box_iff_forall (m := M) (w := w) (φ := φ)).trans ?_
  apply forall_congr'
  intro z
  exact imp_congr_right (fun _ => standardTranslation_correct M φ z)

/-- The sentence `∀x ST_x(φ)` used in Blue Book Prop. 2.47(ii)
(2010 printing, p. 85): universal closure of the only available free variable. -/
def globalTranslation (φ : Cslib.Logic.Modal.Unimodal.Proposition Atom) :
    (language Atom).Sentence :=
  (FirstOrder.Language.BoundedFormula.relabel
    (Sum.inr : Fin 1 → Empty ⊕ Fin 1) (standardTranslation φ)).alls

/-- Blue Book Prop. 2.47(ii), Global Correspondence on Models (2010 printing, p. 85),
specialized to basic unimodal logic over nonempty models.
For every model `M` and modal formula `φ`, truth at all worlds of that same model is equivalent
to satisfaction of the universal closure of its standard translation; this is not frame validity. -/
theorem globalTranslation_correct
    (M : Cslib.Logic.Modal.Unimodal.Model W Atom) [Nonempty W]
    (φ : Cslib.Logic.Modal.Unimodal.Proposition Atom) :
    (∀ w, Cslib.Logic.Modal.Satisfies M w φ) ↔
      (letI : (language Atom).Structure W := toStructure M
       (globalTranslation φ).Realize W) := by
  let : (language Atom).Structure W := toStructure M
  change (∀ w, Cslib.Logic.Modal.Satisfies M w φ) ↔
    (globalTranslation φ).Realize W
  simp only [globalTranslation, FirstOrder.Language.Sentence.Realize,
    FirstOrder.Language.BoundedFormula.realize_alls,
    Nat.add_zero,
    FirstOrder.Language.Formula.realize_relabel_sumInr]
  constructor
  · intro h xs
    have hx : xs = (fun _ => xs 0) := by
      funext j
      exact congrArg xs (Subsingleton.elim j 0)
    rw [hx]
    exact (standardTranslation_correct M φ (xs 0)).mp (h (xs 0))
  · intro h w
    exact (standardTranslation_correct M φ w).mpr (h (fun _ => w))

end ModalCharacterization
