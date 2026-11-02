# Library guide

The main namespace is `ModalCharacterization`; general first-order additions are
under `ModalCharacterization.FirstOrder`. Import `ModalCharacterization` for the
whole library, or import individual modules for a smaller dependency footprint.
Book references below are to Blackburn, de Rijke and Venema, *Modal Logic*, fourth
printing with corrections (2010). See [SOURCES.md](../SOURCES.md) for attribution.

## Semantic conventions

The modal layer uses CSLib's basic unimodal formulas and Kripke models. A modal
model has a binary accessibility relation and a valuation of every atom at every
world. Bisimulations preserve all atoms and satisfy forth/back conditions across
the two models; a pointed bisimilarity witness relates the designated points.
Model satisfaction includes the valuation and is distinct from frame validity.

The main characterization and definability theorems use countable `Atom : Type`.
Their model quantifiers range over all nonempty carriers at a fixed arbitrary
universe `v`, with no finite or countable world restriction. The definability
closure interfaces quantify over both factor worlds and indices in `Type v`;
index-lifting lemmas transport smaller indices explicitly. A pointed model's
designated world supplies nonemptiness. Complements are taken within all pointed
models at the same universe, and the defining formula or formula set is uniform
over that entire class.

Several supporting results are more general: Theorem 2.62 has no atom-countability
premise, while Theorem 2.74 accepts countable `Atom : Type u` and different world
universes. These declarations retain their own universe parameters rather than
inheriting the main theorem's small-language restriction.

## Characterization and definability

- [Modal/VanBenthem.lean](Modal/VanBenthem.lean) proves `vanBenthem`, Theorem 2.68
  (pp. 103–104), with no saturation assumption on the input models. The modal
  consequence argument uses the proved saturation and Detour infrastructure.
- [Modal/Characterization.lean](Modal/Characterization.lean) defines
  `FormulaSemanticallyEquiv`, `ModallyExpressible`, and `BisimulationInvariant`.
  Semantic equivalence quantifies over all nonempty structures in the
  correspondence language. This module proves only the easy implication;
  `VanBenthem.lean` supplies the full equivalence.
- [Modal/Detour.lean](Modal/Detour.lean) proves
  `detour_saturated_ultrapowers`, Lemma 2.66(i) → (iii) (pp. 102–103), and
  `formula_iff_of_modallyEquivalent`. The constructed targets are omega-saturated,
  the diagonal maps are elementary, and the distinguished images are bisimilar.
  The module does not state the full three-way equivalence of Lemma 2.66.
- [Modal/Compactness.lean](Modal/Compactness.lean) supplies the two compactness
  steps for Theorem 2.68: realization of modal consequences at a modally equivalent
  point satisfying the first-order formula, and extraction of a finite conjunction.
  It also transfers finite inconsistency to pointed modal theories for Theorem 2.76.
- [Modal/ModelClass.lean](Modal/ModelClass.lean) defines pointed classes, their
  complements, theory and single-formula definability, and closure under
  bisimulations, heterogeneous ultraproducts, and diagonal ultrapowers. It proves
  the necessary closure properties used in Theorems 2.75–2.76.
- [Modal/ClassCompactness.lean](Modal/ClassCompactness.lean) proves the
  ultraproduct realization argument of Theorem 2.75, Claim 1 (pp. 107–109).
  For a bisimulation- and ultraproduct-closed class, it produces a class member
  modally equivalent to any point satisfying all modal consequences of the class.
- [Modal/Definability.lean](Modal/Definability.lean) proves
  `PointedModelClass.modallyDefinable_iff` (2.75, pp. 107–109) and
  `PointedModelClass.definableByFormula_iff` (2.76, p. 109). The public final
  theorems use the proved Theorem 2.74; no unproved saturation or
  ultrapower-bisimilarity premise remains. Helpers ending in
  `_of_bisimilar_ultrapowers` expose that premise for general compositions.

## Bisimulation, translation, and modal saturation

- [FirstOrder/ModalLanguage.lean](FirstOrder/ModalLanguage.lean) defines the
  correspondence language of Definition 2.44: one binary accessibility relation,
  unary predicates for atoms, and no function symbols. It imports only mathlib,
  although its signature is specific to modal logic.
- [Modal/ModelBridge.lean](Modal/ModelBridge.lean) interprets Kripke models as
  structures in this language and conversely, with explicit model arguments,
  local structure instances, and round-trip lemmas.
- [Modal/Bisimulation.lean](Modal/Bisimulation.lean) implements Definition 2.16
  and cross-model modal invariance (Theorem 2.20). It reuses CSLib's LTS
  forth/back relation and adds atomic agreement and relation nonemptiness.
- [Modal/StandardTranslation.lean](Modal/StandardTranslation.lean) gives the
  binder-aware recursive standard translation (Definition 2.45, p. 84), its local
  correctness theorem `standardTranslation_correct`, and global correctness
  `globalTranslation_correct` (Proposition 2.47(i)–(ii), p. 85). Binder helpers
  track the current world under nested quantifiers. The representation uses
  mathlib's first-order syntax and CSLib's modal syntax.
- [Modal/Saturation.lean](Modal/Saturation.lean) defines modal equivalence and
  modal saturation (Definition 2.53, pp. 92–93), then proves
  `IsModallySaturated.modallyEquivalent_iff_bisimilar` (Proposition 2.54).
  A type finitely satisfiable among a world's successors must be realized among
  those same successors. The empty finite subset still requires a witness.
- [Modal/FirstOrderSaturation.lean](Modal/FirstOrderSaturation.lean) proves
  `isModallySaturated_of_isOmegaSaturated` and the corresponding Hennessy–Milner
  theorem (2.65, p. 102). The proof names the original world as one parameter and
  realizes the type consisting of accessibility and translated modal constraints.
  This implication needs no atom-countability hypothesis.
- [Modal/ImageFinite.lean](Modal/ImageFinite.lean) proves image-finite models
  modally saturated, then derives
  `modallyEquivalent_iff_bisimilar_of_imageFinite`, the conclusion of Theorem 2.24
  (pp. 69–70). Image-finiteness is CSLib's finite-successor condition, not finiteness
  of the whole model. This is a derived proof through Proposition 2.54 rather than
  the book's direct image-finite proof.

## Ultrafilter extensions and ultraproducts

- [Ultrafilter/Relation.lean](Ultrafilter/Relation.lean) supplies mathlib-only
  relation-lifting lemmas, equivalent box/diamond descriptions, principal-point
  behavior, and successor existence by extending the box filter.
- [Modal/UltrafilterExtension.lean](Modal/UltrafilterExtension.lean) constructs
  the frame and model extensions separately (Definition 2.57, p. 94). It proves
  the truth lemma and principal-point modal equivalence (2.59, pp. 96–97), modal
  saturation (2.61, p. 97), and
  `modallyEquivalent_iff_ultrafilterExtension_bisimilar` (2.62, p. 98).
  No countability restriction is imposed on atoms, worlds, or modal types.
  The principal map is not asserted to be elementary or a bounded morphism.
- [Modal/Ultraproduct.lean](Modal/Ultraproduct.lean) constructs heterogeneous modal
  ultraproducts and proves the modal Łoś equivalence by standard translation.
  Indices and factor worlds have independent universe parameters; every factor
  is nonempty.
- [Modal/Ultrapower.lean](Modal/Ultrapower.lean) specializes to constant families,
  proves diagonal modal truth preservation (2.71, pp. 105–106), and supplies the
  modal diagonal elementary embedding. It proves
  `modallyEquivalent_iff_exists_bisimilar_nat_ultrapowers` and
  `modallyEquivalent_iff_exists_bisimilar_ultrapowers` (2.74, pp. 106–107).
  Both powers use one common ultrafilter; the forward construction uses `ℕ`, while
  the reverse implication works with arbitrary index universes.
- [Modal/UltraproductReindex.lean](Modal/UltraproductReindex.lean) proves
  index-lifting bisimulations and transports small-index product and power closure
  into the fixed-universe interfaces for pointed classes.

## First-order infrastructure

These modules use mathlib's syntax, semantics, types, compactness, and ultraproducts.
They do not import CSLib.

- [FirstOrder/PartialTypes.lean](FirstOrder/PartialTypes.lean) relates finite
  realization of a one-variable partial type in a fixed structure to consistency
  with its complete theory, and extends it to a mathlib complete type.
- [FirstOrder/Saturation.lean](FirstOrder/Saturation.lean) defines
  `IsOmegaSaturated` using complete one-types over every finite parameter subset
  of the specified structure. It proves equivalence with finite-realizability and
  consistency formulations (Definition 2.63, p. 101). Realization occurs in that
  same structure; this definition imposes no language-cardinality bound.
- [FirstOrder/Ultrapower.lean](FirstOrder/Ultrapower.lean) proves the diagonal
  elementary embedding `ultrapowerDiagonal` from mathlib's Łoś theorem
  (Corollary A.21, p. 494). This result requires no saturation or countability.
- [FirstOrder/Ultrafilter.lean](FirstOrder/Ultrafilter.lean) relates countable
  incompleteness to decreasing member sets with empty intersection and proves
  that mathlib's `Filter.hyperfilter ℕ` is not a `CountableInterFilter`
  (Example 2.72, p. 106).
- [FirstOrder/UltraproductSaturation.lean](FirstOrder/UltraproductSaturation.lean)
  proves countable partial-type realization with fixed parameters, and
  `ultraproduct_isOmegaSaturated` and `ultrapower_isOmegaSaturated` for countable
  languages over countably incomplete ultrafilters. It follows the diagonal
  selection argument of Chang–Keisler Theorem 6.1.1 and supplies Blue Book
  Lemma 2.73 (p. 106). The omega-saturation conclusion quantifies over finite
  parameter subsets of the ultraproduct itself, not only diagonal parameters.
  It does not restrict factor-world cardinalities or claim arbitrary-cardinal
  saturation.
- [FirstOrder/LanguageCountability.lean](FirstOrder/LanguageCountability.lean)
  is a modal-specific application of mathlib's encoding interfaces: countable atoms give countably many
  correspondence-language symbols and one-variable formulas after naming a finite
  parameter set.

## Verification

From the repository root, `lake build` builds both the library and `Verification`.
The verification entrypoint inspects the main theorem types and transitive axiom
dependencies; supporting regression checks are under `Verification/`. Production
modules never import this layer. The [axiom gate](../Verification/AxiomCheck.lean)
checks every declaration from its imported production and boundary modules,
including private and generated declarations. New modules must be included in
the appropriate library entrypoint and in the gate's explicit `import all` list.
It rejects incomplete private imports and dependencies outside `propext`,
`Classical.choice`, and `Quot.sound`. CI also treats warnings as failures with
`lake build --wfail`. The root [README](../README.md#verification-scope)
states the verification scope and remaining limitations of this snapshot.
