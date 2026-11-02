# Sources and attribution

Project author: **Yiwen Ding**. This library formalizes classical mathematical
results and builds on existing Lean libraries. The notes below distinguish the
mathematical sources, imported dependencies, and related formalization work.

## Mathematical references

- Patrick Blackburn, Maarten de Rijke, and Yde Venema, *Modal Logic*, Cambridge
  University Press, 2001; the source printing used here is the **fourth printing
  with corrections, 2010**. The principal results are Theorems 2.62 (p. 98),
  2.68 (pp. 103–104), 2.74 (pp. 106–107), 2.75 (pp. 107–109), and 2.76 (p. 109).
  Supporting declaration comments give the corresponding definitions,
  propositions, and proof steps. See the
  [authors' book page](https://staff.science.uva.nl/~yde/mlbook/) and
  [published errata](https://staff.science.uva.nl/~yde/mlbook/errata.pdf).
  The source investigation included targeted errata comparisons; it did not
  establish an exhaustive errata audit.
- C. C. Chang and H. J. Keisler, *Model Theory*, **third edition (1990), third
  impression (1992)**, Theorem 6.1.1, pp. 384–385. The countable-type diagonal
  selection proof underlies `FirstOrder/UltraproductSaturation.lean`. The Blue
  Book's Appendix A points Lemma 2.73 to Theorem 6.1.1 in its cited 1973 edition;
  this implementation's proof reference is the later edition specified here.

The van Benthem development uses the book's compactness argument and the
saturated-ultrapower route to the elementary Detour. Only Detour 2.66(i) → (iii)
is implemented as a Detour theorem. The image-finite Hennessy–Milner result is
derived from modal saturation and Proposition 2.54 rather than reproducing the
direct proof of Theorem 2.24. These proof boundaries are also recorded beside
the relevant Lean declarations.

## Imported Lean libraries

- [mathlib](https://github.com/leanprover-community/mathlib4/tree/56a005855ea17e0b0958f73ec801ae140b0a1679),
  revision `56a005855ea17e0b0958f73ec801ae140b0a1679`, supplies first-order syntax,
  semantics, compactness, complete types, elementary embeddings, ultraproducts,
  Łoś's theorem, and filter infrastructure. In particular, the model-theory
  infrastructure used here includes work by **Aaron Anderson**. The filter germ
  infrastructure includes work by **Yury Kudryashov** and
  **Abhimanyu Pallavi Sudhir**. Individual source files retain their author lists
  and Apache-2.0 notices; these examples are not an exhaustive contributor list.
- [CSLib](https://github.com/leanprover/cslib/tree/142f4fa6149aff188630c38d417f00387a3e8b74),
  revision `142f4fa6149aff188630c38d417f00387a3e8b74`, supplies modal syntax and
  semantics, unimodal models, LTS bisimulation, and image-finiteness. Relevant
  modal source authors include **Fabrizio Montesi** and **Marianna Girlando**.
  CSLib already contains related image-finite Hennessy–Milner results for HML,
  with work by **Fabrizio Montesi, Marco Peressotti, and Alexandre Rademaker**.
  Those results are prior formalization work as well as part of the library
  context; the present cross-model, atom-preserving adapter does not make them
  new results. CSLib is licensed under Apache-2.0.

Dependency revisions, including transitive packages, are recorded in
`lake-manifest.json`. The project uses Lean 4.35.0. These are versioned dependency
references, not statements about the latest upstream APIs.

## Prior and related formalizations

**Foundation standard translation.** **Mashu Noguchi** (SnO2WMaN) implemented
modal standard translation and the local and global correctness results of
Blue Book Proposition 2.47 in
[Foundation PR #478](https://github.com/FormalizedFormalLogic/Foundation/pull/478),
merged on 2025-07-24 at `6510ddcb810af60659a37213b422063730a99d0d`.
The historical source inspected is
[`Foundation/Modal/VanBentham/StandardTranslation.lean`](https://github.com/FormalizedFormalLogic/Foundation/blob/c089e7aba19a3c43bf933579b9a7c2965c48fe2e/Foundation/Modal/VanBentham/StandardTranslation.lean)
at revision `c089e7aba19a3c43bf933579b9a7c2965c48fe2e` (Lean 4.29.0).
It uses Foundation's negation-normal modal formulas and first-order syntax.
The implementation was examined as prior work and a source of comparison.
This project's translation instead connects CSLib modal formulas to mathlib
first-order formulas; no Foundation code is copied, ported, or imported here.
Foundation's Apache-2.0 provenance remains relevant to the historical work.
This reference records the inspected version, not a claim about its current build.

**Saturation of ultraproducts.** **Keith J. Bauer** posted a related public draft
in the December 2025
[Saturation of Ultraproducts? discussion](https://leanprover-community.github.io/archive/stream/217875-Is-there-code-for-X%3F/topic/Saturation.20of.20Ultraproducts.3F.html).
The version inspected on 2026-10-11 had an unfinished `ultraproduct_saturation`
proof ending in `sorry`; its statement and parameter interfaces were not a
verified reusable proof of the theorem needed here. The discussion and its
references to existing mathlib APIs informed the source investigation. This
acknowledges the public attempt without claiming that it was complete or making
a statement about later or unpublished work.

**HOL4 modal model theory.** **Yiming Xu and Michael Norrish**, *Mechanised Modal
Model Theory* (2020),
[DOI: 10.1007/978-3-030-51074-9_30](https://doi.org/10.1007/978-3-030-51074-9_30),
and the [associated HOL4 development](https://github.com/u5943321/Modal-Logic)
are prior formalization work in another prover. They are not imported dependencies
of this Lean library, and this release does not claim a checked theorem-by-theorem
comparison with that development.

These references do not support a claim of first formalization or upstream
acceptance.

## License

This project is distributed under [Apache-2.0](LICENSE). Imported dependencies
retain their own licenses, copyright notices, and contributor attribution.
