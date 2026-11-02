/- Modal Characterization in Lean 4. Released under Apache-2.0; see LICENSE. -/
module

public import Verification.Audit
public import Verification.Boundaries
public import Verification.AxiomCheck

/-!
Public verification entry point. Building this module prints the production
theorem types and their transitive axiom dependencies, checks the boundary
regressions, and rejects non-whitelisted axioms in every declaration from the
imported production and boundary modules. These checks do not replace
mathematical review or an independent checker.
-/
