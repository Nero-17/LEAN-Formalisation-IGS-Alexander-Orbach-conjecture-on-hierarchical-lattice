import Universality
import Lean.Elab.Command
import Lean.Util.CollectAxioms

/-!
Executable audit tooling, not a mathematical premise or an additional proof.
Selection follows source-module provenance, including serialized generated and
private project declarations and declarations outside the Universality namespace.
This audit has no `module` header: Lean 4.32.1 imports its transitive closure at
OLeanLevel.private. Thus it checks all serialized project-origin kernel declarations
in the final imported environment. Compiler-only entries absent from the kernel
are counted separately. It does not audit IR safety or hypothetical declarations
that have not been realized and serialized.

Run this source after the final imported closure is verified and frozen.
Importing its compiled object does not rerun the audit command.
-/

open Lean Elab Command in
elab "#audit_project_axioms" : command => do
  let environment ← getEnv
  let approved : Array Name := #[``propext, ``Classical.choice, ``Quot.sound,
    ``Universality.External.gelfond_schneider_real, ``Universality.External.six_exponentials]
  let mut declarations := 0
  let mut modules := 0
  let mut codegenOnly := 0
  let mut gelfondSchneiderDeclarations := 0
  for sourceModule in environment.header.moduleNames do
    if (`Universality).isPrefixOf sourceModule then
      modules := modules + 1
      liftIO <| IO.println ("PROJECT_AXIOM_MODULE " ++ sourceModule.toString)
  for (declarationName, originIndex) in environment.const2ModIdx.toList do
    let sourceModule := environment.header.moduleNames[originIndex]!
    if (`Universality).isPrefixOf sourceModule then
      if (environment.checked.get.find? declarationName).isSome then
        let dependencies ← Lean.collectAxioms declarationName
        for dependency in dependencies do
          unless approved.contains dependency do
            throwError "Unapproved axiom {dependency} in {declarationName}, module {sourceModule}"
        if dependencies.contains ``Universality.External.gelfond_schneider_real then
          gelfondSchneiderDeclarations := gelfondSchneiderDeclarations + 1
        let record := Json.mkObj [
          ("declaration", toJson declarationName.toString),
          ("module", toJson sourceModule.toString),
          ("axioms", toJson (dependencies.map Name.toString))]
        liftIO <| IO.println ("PROJECT_AXIOM_ROW " ++ record.compress)
        declarations := declarations + 1
      else
        codegenOnly := codegenOnly + 1
  if declarations == 0 || modules == 0 then
    throwError "The final project project declaration audit was empty"
  let summary := Json.mkObj [
    ("declarations", toJson declarations), ("modules", toJson modules),
    ("codegen_only", toJson codegenOnly),
    ("gelfond_schneider_declarations", toJson gelfondSchneiderDeclarations)]
  liftIO <| IO.println ("PROJECT_FINAL_KERNEL_AUDIT_OK " ++ summary.compress)

#audit_project_axioms
