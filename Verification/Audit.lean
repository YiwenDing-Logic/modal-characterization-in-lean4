/- Modal Characterization in Lean 4. Released under Apache-2.0; see LICENSE. -/
module

public import ModalCharacterization

/-!
Public type and axiom audit of the implemented basic unimodal cluster.

The `@` checks expose implicit arguments, including typeclass hypotheses;
universe printing makes the world, atom and index sizes visible. Definitions
that determine the quantifier scope are printed before the theorem checks.
Each paired `#print axioms` reports transitive dependencies, to be reviewed
against `propext`, `Classical.choice` and `Quot.sound`.

Source references and proof-route qualifications are attached to the production
declarations. In particular, Detour below is only the (i) to (iii) construction,
and the image-finite result is derived through modal saturation.
-/

set_option pp.universes true
set_option pp.fullNames true

-- Semantic scope: all models and valuations, uniform formula witnesses,
-- finite parameter sets, and the direction of complement ultrapower closure.
#print ModalCharacterization.IsModalBisimulation
#print ModalCharacterization.ModallyBisimilar
#print ModalCharacterization.ModallyEquivalent
#print ModalCharacterization.FormulaSemanticallyEquiv
#print ModalCharacterization.ModallyExpressible
#print ModalCharacterization.BisimulationInvariant
#print ModalCharacterization.IsModallySaturated
#print ModalCharacterization.FirstOrder.IsOmegaSaturated
#print ModalCharacterization.PointedModelClass
#print ModalCharacterization.PointedModelClass.IsModallyDefinable
#print ModalCharacterization.PointedModelClass.IsDefinableByFormula
#print ModalCharacterization.PointedModelClass.ClosedUnderBisimulations
#print ModalCharacterization.PointedModelClass.ClosedUnderUltraproducts
#print ModalCharacterization.PointedModelClass.ClosedUnderUltrapowers

-- Standard translation and bisimulation invariance (2.47 and 2.20).
#check @ModalCharacterization.standardTranslation_correct
#print axioms ModalCharacterization.standardTranslation_correct
#check @ModalCharacterization.globalTranslation_correct
#print axioms ModalCharacterization.globalTranslation_correct
#check @ModalCharacterization.ModallyBisimilar.satisfies_iff
#print axioms ModalCharacterization.ModallyBisimilar.satisfies_iff
#check @ModalCharacterization.ModallyBisimilar.standardTranslation_iff
#print axioms ModalCharacterization.ModallyBisimilar.standardTranslation_iff

-- Hennessy--Milner, its first-order bridge, and the image-finite corollary.
#check @ModalCharacterization.IsModallySaturated.modallyEquivalent_iff_bisimilar
#print axioms ModalCharacterization.IsModallySaturated.modallyEquivalent_iff_bisimilar
#check @ModalCharacterization.isModallySaturated_of_isOmegaSaturated
#print axioms ModalCharacterization.isModallySaturated_of_isOmegaSaturated
#check @ModalCharacterization.modallyEquivalent_iff_bisimilar_of_isOmegaSaturated
#print axioms ModalCharacterization.modallyEquivalent_iff_bisimilar_of_isOmegaSaturated
#check @ModalCharacterization.isModallySaturated_of_imageFinite
#print axioms ModalCharacterization.isModallySaturated_of_imageFinite
#check @ModalCharacterization.modallyEquivalent_iff_bisimilar_of_imageFinite
#print axioms ModalCharacterization.modallyEquivalent_iff_bisimilar_of_imageFinite

-- Ultrafilter extension truth, saturation, and bisimulation somewhere (2.62).
#check @ModalCharacterization.ultrafilterExtension_truth
#print axioms ModalCharacterization.ultrafilterExtension_truth
#check @ModalCharacterization.modallyEquivalent_ultrafilterExtension_pure
#print axioms ModalCharacterization.modallyEquivalent_ultrafilterExtension_pure
#check @ModalCharacterization.ultrafilterExtension_isModallySaturated
#print axioms ModalCharacterization.ultrafilterExtension_isModallySaturated
#check @ModalCharacterization.modallyEquivalent_iff_ultrafilterExtension_bisimilar
#print axioms ModalCharacterization.modallyEquivalent_iff_ultrafilterExtension_bisimilar

-- Partial types and saturated ultrapowers: these are existence results,
-- in addition to the saturation definitions printed above.
#check @ModalCharacterization.FirstOrder.finitelyRealized_iff_isSatisfiable
#print axioms ModalCharacterization.FirstOrder.finitelyRealized_iff_isSatisfiable
#check @ModalCharacterization.FirstOrder.exists_completeType_of_finitelyRealized
#print axioms ModalCharacterization.FirstOrder.exists_completeType_of_finitelyRealized
#check @ModalCharacterization.FirstOrder.isOmegaSaturated_iff_realizes_consistent
#print axioms ModalCharacterization.FirstOrder.isOmegaSaturated_iff_realizes_consistent
#check @ModalCharacterization.FirstOrder.ultrapowerDiagonal
#print axioms ModalCharacterization.FirstOrder.ultrapowerDiagonal
#check @ModalCharacterization.FirstOrder.nat_hyperfilter_not_countableInterFilter
#print axioms ModalCharacterization.FirstOrder.nat_hyperfilter_not_countableInterFilter
#check @ModalCharacterization.FirstOrder.ultraproduct_isOmegaSaturated
#print axioms ModalCharacterization.FirstOrder.ultraproduct_isOmegaSaturated
#check @ModalCharacterization.FirstOrder.ultrapower_isOmegaSaturated
#print axioms ModalCharacterization.FirstOrder.ultrapower_isOmegaSaturated

-- Modal ultraproducts, diagonal elementarity, and bisimulation somewhere (2.74).
#check @ModalCharacterization.satisfies_modalUltraproduct
#print axioms ModalCharacterization.satisfies_modalUltraproduct
#check @ModalCharacterization.modalUltrapowerDiagonal
#print axioms ModalCharacterization.modalUltrapowerDiagonal
#check @ModalCharacterization.satisfies_modalUltrapower_diagonal
#print axioms ModalCharacterization.satisfies_modalUltrapower_diagonal
#check @ModalCharacterization.modalUltrapower_isOmegaSaturated
#print axioms ModalCharacterization.modalUltrapower_isOmegaSaturated
#check @ModalCharacterization.modallyEquivalent_iff_exists_bisimilar_nat_ultrapowers
#print axioms ModalCharacterization.modallyEquivalent_iff_exists_bisimilar_nat_ultrapowers
#check @ModalCharacterization.modallyEquivalent_iff_exists_bisimilar_ultrapowers
#print axioms ModalCharacterization.modallyEquivalent_iff_exists_bisimilar_ultrapowers

-- Compactness, the required Detour direction, and van Benthem (2.68).
#check @ModalCharacterization.exists_finite_unsatisfiable_of_unsatisfiable
#print axioms ModalCharacterization.exists_finite_unsatisfiable_of_unsatisfiable
#check @ModalCharacterization.modallyExpressible_of_modal_consequences_entail
#print axioms ModalCharacterization.modallyExpressible_of_modal_consequences_entail
#check @ModalCharacterization.detour_saturated_ultrapowers
#print axioms ModalCharacterization.detour_saturated_ultrapowers
#check @ModalCharacterization.formula_iff_of_modallyEquivalent
#print axioms ModalCharacterization.formula_iff_of_modallyEquivalent
#check @ModalCharacterization.vanBenthem
#print axioms ModalCharacterization.vanBenthem

-- Pointed-model class compactness and the unconditional 2.75/2.76 results.
#check @ModalCharacterization.PointedModelClass.exists_realization_of_finitely_satisfiable
#print axioms ModalCharacterization.PointedModelClass.exists_realization_of_finitely_satisfiable
#check @ModalCharacterization.PointedModelClass.modallyDefinable_iff
#print axioms ModalCharacterization.PointedModelClass.modallyDefinable_iff
#check @ModalCharacterization.PointedModelClass.definableByFormula_iff
#print axioms ModalCharacterization.PointedModelClass.definableByFormula_iff
