/- Modal Characterization in Lean. Released under Apache-2.0; see LICENSE. -/
module

public meta import Lean.Elab.Command
public meta import Lean.Util.CollectAxioms

-- `import all` is required separately for each module: it does not propagate
-- through an ordinary import. The coverage check below rejects an incomplete
-- import if a further production module is added to the import graph.
import all ModalCharacterization
import all ModalCharacterization.FirstOrder.LanguageCountability
import all ModalCharacterization.FirstOrder.ModalLanguage
import all ModalCharacterization.FirstOrder.PartialTypes
import all ModalCharacterization.FirstOrder.Saturation
import all ModalCharacterization.FirstOrder.Ultrafilter
import all ModalCharacterization.FirstOrder.Ultrapower
import all ModalCharacterization.FirstOrder.UltraproductSaturation
import all ModalCharacterization.Modal.Bisimulation
import all ModalCharacterization.Modal.Characterization
import all ModalCharacterization.Modal.ClassCompactness
import all ModalCharacterization.Modal.Compactness
import all ModalCharacterization.Modal.Definability
import all ModalCharacterization.Modal.Detour
import all ModalCharacterization.Modal.FirstOrderSaturation
import all ModalCharacterization.Modal.ImageFinite
import all ModalCharacterization.Modal.ModelBridge
import all ModalCharacterization.Modal.ModelClass
import all ModalCharacterization.Modal.Saturation
import all ModalCharacterization.Modal.StandardTranslation
import all ModalCharacterization.Modal.UltrafilterExtension
import all ModalCharacterization.Modal.Ultrapower
import all ModalCharacterization.Modal.Ultraproduct
import all ModalCharacterization.Modal.UltraproductReindex
import all ModalCharacterization.Modal.VanBenthem
import all ModalCharacterization.Ultrafilter.Relation
import all Verification.Audit
import all Verification.Boundaries

/-!
Failing CI gate for the transitive axiom dependencies of every declaration in
the imported production and boundary modules, including private declarations
and generated auxiliaries. Selection uses the defining **module**, not the
declaration's namespace or a fixed list of theorem names.

This is an implementation check, not a numbered result of the Blue Book.
It uses the pinned Lean 4.35.0 `collectAxioms` API, also used by `#print axioms`.
That API uses the imported axiom metadata and, when needed, the checked
environment's declaration types and bodies. The gate rejects every axiom
except `propext`, `Classical.choice`, and `Quot.sound`; in particular, neither
`sorryAx` nor a fresh project axiom is allowed.

The gate checks the imported module graph, not unimported source files. New
production modules must enter the production root and the `import all` list
above. This axiom policy check does not replace checking mathematical statement
fidelity, proof-route review, kernel replay, or an independent implementation
of a proof checker. It does not change Lean's trust level or kernel checks.
-/

public meta section

namespace Verification.AxiomCheck

open Lean Elab Command

/-- Implementation policy for this project's axiom audit; not a mathematical
definition or an assertion that these foundations suffice for semantic review. -/
def isAllowedAxiom (name : Name) : Bool :=
  name == ``propext || name == ``Classical.choice || name == ``Quot.sound

/-- Implementation check of an explicit nonempty declaration selection. Unknown
names and forbidden transitive dependencies are errors. This entry point also
permits negative checks in separate scratch modules, without adding test axioms
or unfinished proofs to the production dependency graph. -/
def checkDeclarations (names : Array Name) : CommandElabM Unit := do
  if names.isEmpty then
    throwError "Axiom check failed: the declaration selection is empty"
  let env := (← getEnv).setExporting false
  let mut failures : Nat := 0
  for name in names.qsort Name.lt do
    unless (env.checked.get.find? name).isSome do
      throwError "Axiom check failed: declaration {name} is absent from the checked environment"
    let forbidden := (← collectAxioms name).filter fun ax => !isAllowedAxiom ax
    unless forbidden.isEmpty do
      failures := failures + 1
      let dependencies := MessageData.joinSep
        (forbidden.toList.map fun ax => m!"{ax}") ", "
      logError m!"Axiom check failed for {name}: forbidden transitive axioms [{dependencies}]"
  unless failures == 0 do
    throwError "Axiom check rejected {failures} declaration(s)"

/-- Implementation coverage check: select all declarations by the origin module
recorded in Lean's environment. Require complete private imports before scanning,
and fail if either the module selection or declaration selection is empty. -/
def checkImportedModules (selectModule : Name → Bool) : CommandElabM Unit := do
  let env := (← getEnv).setExporting false
  let modules := env.header.modules.filter fun imported => selectModule imported.module
  if modules.isEmpty then
    throwError "Axiom check failed: the imported module selection is empty"
  for imported in modules do
    unless imported.hasData && imported.importAll do
      throwError "Axiom check failed: use `import all {imported.module}` to include private declarations"
  let moduleNames := env.header.moduleNames
  let mut names := #[]
  for (name, _) in env.constants do
    if let some index := env.getModuleIdxFor? name then
      let some origin := moduleNames[index.toNat]?
        | throwError "Axiom check failed: missing origin module for {name}"
      if selectModule origin then
        names := names.push name
  checkDeclarations names
  logInfo m!"Axiom check passed: {names.size} declarations from {modules.size} fully imported modules; allowed axioms: propext, Classical.choice, Quot.sound"

/-- Build-time implementation check of all imported production and verification
modules. Module prefixes are used only to choose source modules; declarations
are included regardless of namespace, visibility, or generated names. -/
elab "#check_project_axioms" : command =>
  checkImportedModules fun name =>
    (`ModalCharacterization).isPrefixOf name || (`Verification).isPrefixOf name

end Verification.AxiomCheck

#check_project_axioms
