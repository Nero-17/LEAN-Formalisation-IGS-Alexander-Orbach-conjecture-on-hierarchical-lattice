import IGSAlexanderOrbach
import Lean
open Lean Elab Command
set_option maxHeartbeats 0
run_cmd do
  let environment ← getEnv
  let mut audited : Nat := 0
  for moduleName in environment.allImportedModuleNames do
    if (`IGSIII34).isPrefixOf moduleName || (`IGSIII).isPrefixOf moduleName || (`IGSIII4).isPrefixOf moduleName || moduleName == `IGSIIISectionsThreeFour || moduleName == `IGSIIISectionsTwoThreeFour || moduleName == `IGSAlexanderOrbach then
      logInfo m!"IMPORTED {moduleName}"
  for (declaration, _) in environment.constants do
    if let some moduleIndex := environment.getModuleIdxFor? declaration then
      let moduleName := environment.allImportedModuleNames[moduleIndex.toNat]!
      if (`IGSIII34).isPrefixOf moduleName || (`IGSIII).isPrefixOf moduleName || (`IGSIII4).isPrefixOf moduleName || moduleName == `IGSIIISectionsThreeFour || moduleName == `IGSIIISectionsTwoThreeFour || moduleName == `IGSAlexanderOrbach then
        let axioms ← collectAxioms declaration
        for axiomName in axioms do
          unless axiomName == `propext || axiomName == `Classical.choice || axiomName == `Quot.sound do
            throwError "Unexpected axiom {axiomName} in {declaration}"
        logInfo m!"AUDITED {moduleName} {declaration}: {axioms}"
        audited := audited + 1
  if audited == 0 then throwError "No project declarations audited"
  for target in #[`IGSIII4.section_four_for_natural_resistance,
      `IGSIII4.exists_section_four_from_proved_sections_two_three,
      `IGSIII4.natural_critical_supersolution,
      `IGSIII4.natural_long_diamond_spectral_dimension_strictly_below_four_thirds,
      `IGSIII4.exists_ae_actual_section_four_typical_heat_kernel,
      `IGSIII4.exists_actual_section_four_and_typical_heat_kernel,
      `IGSIII.Geometry.exists_actual_critical_section_two_geometry,
      `IGSIII34.Diffusion.exists_actual_intrinsic_component_diameter_envelopes20261011,
      `IGSIII34.Spectral.actualSpectralData_positive_laplace_variational_completion20261011,
      `IGSIII.Chemical.Substitution.exists_actual_raw_prefix_conditional_variance_rate20261011] do
    let some information := environment.find? target | throwError "Missing actual interface {target}"
    let mut type := information.type
    let mut parameters : Nat := 0
    let mut scanning := true
    let mut parameterPosition : Option Nat := none
    let mut positiveParameterChecked := false
    while scanning do
      match type with
      | .forallE binder domain body _ =>
        if target == `IGSIII34.Spectral.actualSpectralData_positive_laplace_variational_completion20261011 then
          if binder == `parameter then parameterPosition := some parameters
          if binder == `parameterPositive then
            let some position := parameterPosition | throwError "Positive-parameter interface has no preceding parameter binder"
            let arguments := domain.getAppArgs
            unless domain.isAppOf `LT.lt && arguments.size >= 2 do
              throwError "Positive-parameter interface does not assume strict positivity"
            let left := arguments[arguments.size - 2]!
            let right := arguments[arguments.size - 1]!
            let numeralArguments := left.getAppArgs
            unless left.isAppOf `OfNat.ofNat && numeralArguments.size >= 2 &&
                numeralArguments[1]! == .lit (.natVal 0) &&
                right == .bvar (parameters - position - 1) do
              throwError "Positive-parameter input is not exactly 0 < parameter"
            positiveParameterChecked := true
          if domain.isAppOf `LE.le then
            let arguments := domain.getAppArgs
            if let some position := parameterPosition then
              if arguments.size >= 2 && arguments[arguments.size - 1]! == .bvar (parameters - position - 1) then
                throwError "A lower-bound premise remains on the all-positive resolvent parameter"
        if #[`accepted, `upper, `pruning, `acceptedSectionThreeFormula].contains binder then
          throwError "Former assumed input {binder} remains in {target}"
        if let .const domainName _ := domain.getAppFn then
          if #[`IGSIII4.AcceptedElectricalSectionThree,
              `IGSIII4.AcceptedResistanceMeanUpperSectionThree,
              `IGSIII4.AcceptedCorePruningSectionThree].contains domainName then
            throwError "Former assumed certificate {domainName} remains in {target}"
        type := body
        parameters := parameters + 1
      | _ => scanning := false
    if target == `IGSIII4.exists_section_four_from_proved_sections_two_three ||
        target == `IGSIII4.exists_actual_section_four_and_typical_heat_kernel ||
        target == `IGSIII34.Diffusion.exists_actual_intrinsic_component_diameter_envelopes20261011 ||
        target == `IGSIII.Geometry.exists_actual_critical_section_two_geometry ||
        target == `IGSIII.Chemical.Substitution.exists_actual_raw_prefix_conditional_variance_rate20261011 then
      unless parameters == 6 do
        throwError "The final model-only theorem {target} has {parameters} inputs, expected six"
    if target == `IGSIII34.Spectral.actualSpectralData_positive_laplace_variational_completion20261011 then
      unless positiveParameterChecked do throwError "Missing all-positive resolvent premise"
      logInfo m!"POSITIVE_PARAMETER_INTERFACE {target} EXACT_ZERO_LT_PARAMETER"
    logInfo m!"ACTUAL_INTERFACE {target} PARAMETERS {parameters}"
  logInfo m!"AUDIT_TOTAL {audited}"
