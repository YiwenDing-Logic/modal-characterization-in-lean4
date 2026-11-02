# Modal Characterization in Lean 4

[![Lean CI](https://github.com/YiwenDing-Logic/modal-characterization-in-lean4/actions/workflows/lean.yml/badge.svg)](https://github.com/YiwenDing-Logic/modal-characterization-in-lean4/actions/workflows/lean.yml)

A Lean 4 library for classical modal model theory, built on mathlib and CSLib.
It formalizes van Benthem's characterization theorem together with
bisimulation-somewhere characterizations, modal definability of pointed model
classes, Hennessy–Milner results, and their saturation and ultraproduct foundations.

The development specializes to **basic unimodal logic**. Its characterization
theorems range over all nonempty world domains at the stated universes; worlds
are not assumed finite or countable. The mathematical reference is Blackburn,
de Rijke and Venema, *Modal Logic*, fourth printing with corrections (2010).

## Results

- **Van Benthem characterization, Theorem 2.68:** a first-order formula with at
  most one free variable is bisimulation invariant iff it is equivalent to the
  standard translation of one modal formula. This uses countable `Atom : Type`
  and all nonempty models at an arbitrary fixed world universe.
  See [VanBenthem.lean](ModalCharacterization/Modal/VanBenthem.lean).
- **Bisimulation somewhere via ultrafilter extensions, Theorem 2.62:** two points
  are modally equivalent iff their principal ultrafilters are bisimilar in the
  respective ultrafilter extensions. This includes the truth lemma (2.59) and
  modal saturation (2.61), without countability assumptions on atoms or worlds.
  See [UltrafilterExtension.lean](ModalCharacterization/Modal/UltrafilterExtension.lean).
- **Bisimulation somewhere via ultrapowers, Theorem 2.74:** two points are modally
  equivalent iff their diagonal images are bisimilar in ultrapowers using one
  common index type and ultrafilter. Atoms are countable; world domains may have
  different universes. The construction already works with index type `ℕ`.
  See [Ultrapower.lean](ModalCharacterization/Modal/Ultrapower.lean).
- **Definability by a set of modal formulas, Theorem 2.75:** a pointed model class
  is definable iff it is closed under bisimulations and ultraproducts, and its
  complement is closed under ultrapowers.
- **Definability by one modal formula, Theorem 2.76:** a pointed model class is
  definable by one formula iff both the class and its complement are closed under
  bisimulations and ultraproducts. Both definability theorems use countable
  `Atom : Type`, with worlds and closure indices at an arbitrary fixed universe.
  See [Definability.lean](ModalCharacterization/Modal/Definability.lean).
- **Hennessy–Milner and saturation:** the saturated-model theorem (2.54),
  first-order omega-saturation implying modal saturation and the Hennessy–Milner
  property (2.65), and the image-finite conclusion of Theorem 2.24.
  See [Saturation.lean](ModalCharacterization/Modal/Saturation.lean),
  [FirstOrderSaturation.lean](ModalCharacterization/Modal/FirstOrderSaturation.lean),
  and [ImageFinite.lean](ModalCharacterization/Modal/ImageFinite.lean).
- **Foundations:** bisimulation invariance (2.20), local and global standard
  translation correctness (2.47), compactness bridges, elementary diagonal
  embeddings into ultrapowers (A.21), and omega-saturation of suitable
  ultraproducts and ultrapowers (2.73).

These are results about models and pointed model classes. The library does not
contain a proof of the Goldblatt–Thomason theorem about frame classes.

## Main theorem

In the namespace `ModalCharacterization`, with world universe `v`, the main
declaration is:

```lean
theorem vanBenthem
    {Atom : Type} [Countable Atom] (α : (language Atom).Formula (Fin 1)) :
    BisimulationInvariant.{0, v} α ↔ ModallyExpressible.{0, v} α
```

The correspondence language has one binary accessibility relation and one unary
predicate per propositional letter. `Fin 1` supplies the sole possible free
variable. `ModallyExpressible` chooses a single modal formula before quantifying
over every nonempty first-order structure and designated world at universe `v`.
The two models in `BisimulationInvariant` have independent relations and
valuations. See [Characterization.lean](ModalCharacterization/Modal/Characterization.lean)
for these semantic definitions.

## Proof organization

The van Benthem proof follows the modal-consequence and compactness argument of
Theorem 2.68 (pp. 103–104). Its elementary Detour uses saturated ultrapowers:
Lemma 2.73, first-order-to-modal saturation (2.65), and the Hennessy–Milner
property give Theorem 2.74; elementary diagonal embeddings transfer first-order
truth. Two compactness steps then produce a finite modal conjunction.

[Detour.lean](ModalCharacterization/Modal/Detour.lean) implements
Lemma 2.66 **(i) → (iii)**, retaining saturation and elementary embeddings, together
with the truth-transfer consequence used by van Benthem. It does not claim the
full three-way Detour equivalence. The image-finite Hennessy–Milner theorem is
derived by proving image-finite models modally saturated and applying Proposition
2.54; it does not reproduce the direct proof of Theorem 2.24.

General first-order infrastructure depends only on mathlib. CSLib-dependent modal
adapters form a separate layer. The [module guide](ModalCharacterization/README.md)
describes the interfaces, hypotheses, and source correspondence.

## Build and inspect

Install the Lean version specified in `lean-toolchain`, then run from the
repository root:

```sh
lake build
```

The default targets are `ModalCharacterization` and `Verification`. The former
imports the complete library; the latter checks principal theorem types and
prints transitive axiom dependencies in [Verification/Audit.lean](Verification/Audit.lean),
with semantic regression checks in [Verification/Boundaries.lean](Verification/Boundaries.lean).
The [axiom gate](Verification/AxiomCheck.lean) rejects any transitive axiom other
than `propext`, `Classical.choice`, and `Quot.sound` in the imported production
and boundary modules, including private declarations and generated auxiliaries.
Library modules do not import verification modules. To use the library, write:

```lean
import ModalCharacterization
```

The reproducible dependency pins are:

- Lean **4.35.0**.
- mathlib [`56a005855ea17e0b0958f73ec801ae140b0a1679`](https://github.com/leanprover-community/mathlib4/tree/56a005855ea17e0b0958f73ec801ae140b0a1679).
- CSLib [`142f4fa6149aff188630c38d417f00387a3e8b74`](https://github.com/leanprover/cslib/tree/142f4fa6149aff188630c38d417f00387a3e8b74).

`lake-manifest.json` records the transitive dependency revisions. Compatibility
with other revisions is not asserted.

## Continuous integration

The [Lean CI workflow](.github/workflows/lean.yml) runs on pushes to `main`, pull
requests, and manual dispatch. It builds both default targets on Ubuntu 24.04
with the pinned Lean version and dependencies. The build command is:

```sh
lake build --wfail
```

Warnings fail the build, as do axiom-policy violations. Public regression checks
run through the `Verification` target. The workflow downloads mathlib's dependency
cache but does not restore a GitHub cache of this project's build artifacts.
Action references are pinned to full commits, repository permissions are read-only,
and a final step checks that the toolchain, Lake configuration, and dependency
lockfile have not changed during the build. This workflow does not publish or deploy.

## Verification scope

On 2026-11-02, `lake build --wfail` passed both default targets for this snapshot,
including all 26 production modules, 34 production declaration audits, and six
semantic boundary regressions. In addition to these 40 explicit listings, the
axiom gate accepted all 224 declarations from 28 fully imported production and
verification modules. Their axiom dependencies are subsets of `propext`,
`Classical.choice`, and `Quot.sound`.

The build used a new project build directory and cached dependencies whose
revisions matched the lockfile. It was not a fresh dependency reconstruction or
an isolated validation run. The verification entrypoint exposes the theorem
types and actual axiom dependencies for inspection. On 2026-11-02, hosted
GitHub CI also passed on Ubuntu 24.04: all 1145 build jobs completed,
the axiom gate accepted the same 224 declarations, and the dependency pins
remained unchanged. The badge above links to current CI results.
Independent-checker validation and isolated validation of this snapshot have not
been completed. Compilation and axiom checks do not by themselves establish that
the formal statements faithfully express the source mathematics.

## Attribution and license

Project author: **Yiwen Ding**. Mathematical references, dependency authorship,
and prior formalizations are documented in [SOURCES.md](SOURCES.md).
This project is licensed under [Apache-2.0](LICENSE).
