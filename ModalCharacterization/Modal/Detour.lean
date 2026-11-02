/- Modal Characterization in Lean. Released under Apache-2.0; see LICENSE.
Uses mathlib model theory and CSLib modal semantics; no experimental imports. -/
module
public import ModalCharacterization.Modal.Ultrapower
public import ModalCharacterization.Modal.Characterization

@[expose] public section
namespace ModalCharacterization
open _root_.FirstOrder _root_.FirstOrder.Language Cslib.Logic.Modal
universe u v w z

/-- Detour Lemma 2.66(i) → (iii) (2010 fourth corrected printing,
pp. 102–103), via the ultrapower route of Thm. 2.74. Specialized to the agreed
countable basic unimodal language. The output retains BOTH saturation claims,
explicit elementary embeddings, and bisimilarity of the images of the specified
points. The models are the chosen ultrapowers, and the distinguished points
are `f x` and `g y`, so clause (iii)(a) is built into the conclusion.
Uses Lemma 2.73. This is the (i) to (iii) construction needed for Thm. 2.68,
not the full three-way equivalence, nor a literal inclusion of carriers. -/
theorem detour_saturated_ultrapowers
    {Atom : Type u} [Countable Atom] {W : Type v} {W' : Type w}
    (M : Unimodal.Model W Atom) (N : Unimodal.Model W' Atom)
    [Nonempty W] [Nonempty W'] (x : W) (y : W')
    (h : ModallyEquivalent M N x y) :
    ∃ U : Ultrafilter ℕ,
      (letI : (language Atom).Structure W := toStructure M
       letI : (language Atom).Structure ((U : Filter ℕ).Product (fun _ : ℕ => W)) :=
         toStructure (modalUltrapower M U)
       FirstOrder.IsOmegaSaturated (language Atom)
         ((U : Filter ℕ).Product (fun _ : ℕ => W))) ∧
      (letI : (language Atom).Structure W' := toStructure N
       letI : (language Atom).Structure ((U : Filter ℕ).Product (fun _ : ℕ => W')) :=
         toStructure (modalUltrapower N U)
       FirstOrder.IsOmegaSaturated (language Atom)
         ((U : Filter ℕ).Product (fun _ : ℕ => W'))) ∧
      ∃ (f : letI : (language Atom).Structure W := toStructure M
             @ElementaryEmbedding (language Atom) W
               ((U : Filter ℕ).Product (fun _ : ℕ => W))
               (toStructure M) (toStructure (modalUltrapower M U)))
        (g : letI : (language Atom).Structure W' := toStructure N
             @ElementaryEmbedding (language Atom) W'
               ((U : Filter ℕ).Product (fun _ : ℕ => W'))
               (toStructure N) (toStructure (modalUltrapower N U))),
        ModallyBisimilar (modalUltrapower M U) (modalUltrapower N U)
          (letI : (language Atom).Structure W := toStructure M
           letI : (language Atom).Structure ((U : Filter ℕ).Product (fun _ : ℕ => W)) :=
             toStructure (modalUltrapower M U)
           f x)
          (letI : (language Atom).Structure W' := toStructure N
           letI : (language Atom).Structure ((U : Filter ℕ).Product (fun _ : ℕ => W')) :=
             toStructure (modalUltrapower N U)
           g y) := by
  let U := Filter.hyperfilter ℕ
  have hU : ¬ CountableInterFilter (U : Filter ℕ) :=
    FirstOrder.nat_hyperfilter_not_countableInterFilter
  refine ⟨U, modalUltrapower_isOmegaSaturated M U hU,
    modalUltrapower_isOmegaSaturated N U hU,
    modalUltrapowerDiagonal M U, modalUltrapowerDiagonal N U, ?_⟩
  apply (modallyEquivalent_iff_bisimilar_of_isOmegaSaturated
    (modalUltrapower M U) (modalUltrapower N U)
    (modalUltrapower_isOmegaSaturated M U hU)
    (modalUltrapower_isOmegaSaturated N U hU)).mp
  exact (modallyEquivalent_diagonal_iff M N U x y).mpr h

/-- Last Detour step of Blue Book Thm. 2.68 (2010 fourth corrected printing,
p. 104), countable basic unimodal language. Elementary embeddings preserve and
reflect the arbitrary first-order formula; bisimulation invariance connects their
image points. Both original carriers have the same arbitrary universe, and the
natural-number ultrapowers stay there. Uses the now-proved Lemma 2.73. -/
theorem formula_iff_of_modallyEquivalent
    {Atom : Type u} [Countable Atom]
    (α : (language Atom).Formula (Fin 1)) (hinv : BisimulationInvariant.{u, v} α)
    {W W' : Type v} [Nonempty W] [Nonempty W']
    (M : Unimodal.Model W Atom) (N : Unimodal.Model W' Atom)
    (x : W) (y : W') (h : ModallyEquivalent M N x y) :
    holds M α x ↔ holds N α y := by
  obtain ⟨U, _, _, f, g, hb⟩ := detour_saturated_ultrapowers M N x y h
  let : (language Atom).Structure W := toStructure M
  let : (language Atom).Structure W' := toStructure N
  let : (language Atom).Structure ((U : Filter ℕ).Product (fun _ : ℕ => W)) :=
    toStructure (modalUltrapower M U)
  let : (language Atom).Structure ((U : Filter ℕ).Product (fun _ : ℕ => W')) :=
    toStructure (modalUltrapower N U)
  have hf : holds (modalUltrapower M U) α (f x) ↔ holds M α x :=
    f.map_formula α (fun _ => x)
  have hg : holds (modalUltrapower N U) α (g y) ↔ holds N α y :=
    g.map_formula α (fun _ => y)
  exact hf.symm.trans ((hinv _ _ (modalUltrapower M U) (modalUltrapower N U)
    (f x) (g y) hb).trans hg)

end ModalCharacterization
