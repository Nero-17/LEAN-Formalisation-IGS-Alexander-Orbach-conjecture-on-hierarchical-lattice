import IGSAlexanderOrbach
import Lean

open Lean Elab Command
set_option maxHeartbeats 0

/-! Check every declaration defined by a packaged module, including private
and generated declarations, allowing only Lean's three standard axioms. -/
run_cmd do
  let environment ← getEnv
  let mut audited : Nat := 0
  for (declaration, _) in environment.constants do
    if let some moduleIndex := environment.getModuleIdxFor? declaration then
      let moduleName := environment.allImportedModuleNames[moduleIndex.toNat]!
      if (`Universality).isPrefixOf moduleName || (`IGSIII).isPrefixOf moduleName ||
          (`IGSIII34).isPrefixOf moduleName || (`IGSIII4).isPrefixOf moduleName then
        let axioms ← collectAxioms declaration
        for axiomName in axioms do
          unless axiomName == `propext || axiomName == `Classical.choice || axiomName == `Quot.sound do
            throwError "Unexpected axiom {axiomName} in {declaration}"
        audited := audited + 1
  if audited == 0 then throwError "No package declarations audited"
  logInfo m!"AUDIT_TOTAL {audited}; only propext, Classical.choice and Quot.sound"
