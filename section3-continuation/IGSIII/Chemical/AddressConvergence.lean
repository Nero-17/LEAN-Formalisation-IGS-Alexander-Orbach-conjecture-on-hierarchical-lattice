import IGSIII.Chemical.TerminalEnvelope
import IGSIII.Chemical.OrbitLpConvergence

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 600000

namespace IGSIII.Chemical.Substitution

open Universality Universality.FiniteNetwork MeasureTheory Filter IGSIII.Probability IGSIII.Geometry
open scoped ENNReal Topology

theorem chemicalOrbit_shift_eq_terminalScaledDistance_ae
    (rule : Rule) (classical : rule.Classical)
    (p : ℝ) (positive : 0 < p) (belowOne : p < 1)
    (fixedPoint : rule.network.reliability p = p) (growth : ℝ) (growthPositive : 0 < growth) :
    ∀ᵐ marks ∂independentInnovationLaw rule p positive belowOne fixedPoint, ∀ address depth,
      chemicalOrbit rule p positive belowOne fixedPoint growth (depth + 1) (innovationTreeShift rule address marks) =
        (markedTerminalDistance rule marks depth address true : ℝ) / growth ^ (depth + 1) := by
  have rootValues : ∀ᵐ marks ∂independentInnovationLaw rule p positive belowOne fixedPoint, ∀ depth,
      chemicalOrbit rule p positive belowOne fixedPoint growth depth marks = growth⁻¹ ^ depth *
        ((chemicalTransfer rule)^[depth] (fun _ => 1)) marks :=
    ae_all_iff.mpr (fun depth => normalizedChemicalTransferLp_iterate_ae rule p positive belowOne fixedPoint
      2 growth growthPositive.le depth)
  have shiftedValues : ∀ᵐ marks ∂independentInnovationLaw rule p positive belowOne fixedPoint, ∀ address depth,
      chemicalOrbit rule p positive belowOne fixedPoint growth depth (innovationTreeShift rule address marks) = growth⁻¹ ^ depth *
        ((chemicalTransfer rule)^[depth] (fun _ => 1)) (innovationTreeShift rule address marks) :=
    ae_all_iff.mpr (fun address =>
      (innovationTreeShift_preserving rule p positive belowOne fixedPoint address).quasiMeasurePreserving.ae rootValues)
  filter_upwards [shiftedValues, chemicalTransfer_iterate_eq_actual_ae rule classical.simple p positive belowOne fixedPoint]
    with marks values actual
  intro address depth
  rw [values address (depth + 1), actual depth address]
  unfold markedTerminalDistance
  rw [inv_pow]
  ring

theorem chemical_terminal_field_ae_convergence_of_orbit_convergence
    (rule : Rule) (classical : rule.Classical)
    (p : ℝ) (positive : 0 < p) (belowOne : p < 1)
    (fixedPoint : rule.network.reliability p = p) (growth : ℝ) (growthPositive : 0 < growth)
    (value : Lp ℝ 2 (independentInnovationLaw rule p positive belowOne fixedPoint)) (amplitude : ℝ)
    (convergence : ∀ᵐ marks ∂independentInnovationLaw rule p positive belowOne fixedPoint,
      Tendsto (fun depth => chemicalOrbit rule p positive belowOne fixedPoint growth depth marks)
        atTop (𝓝 ((amplitude • value) marks))) :
    ∀ᵐ marks ∂independentInnovationLaw rule p positive belowOne fixedPoint, ∀ address,
      Tendsto (fun depth => (markedTerminalDistance rule marks depth address true : ℝ) / growth ^ (depth + 1))
        atTop (𝓝 (amplitude * chemicalField rule p positive belowOne fixedPoint value address marks)) := by
  have shiftedConvergence : ∀ᵐ marks ∂independentInnovationLaw rule p positive belowOne fixedPoint, ∀ address,
      Tendsto (fun depth => chemicalOrbit rule p positive belowOne fixedPoint growth depth (innovationTreeShift rule address marks))
        atTop (𝓝 ((amplitude • value) (innovationTreeShift rule address marks))) :=
    ae_all_iff.mpr (fun address =>
      (innovationTreeShift_preserving rule p positive belowOne fixedPoint address).quasiMeasurePreserving.ae convergence)
  have shiftedScalars : ∀ᵐ marks ∂independentInnovationLaw rule p positive belowOne fixedPoint, ∀ address,
      (amplitude • value) (innovationTreeShift rule address marks) =
        amplitude * chemicalField rule p positive belowOne fixedPoint value address marks :=
    ae_all_iff.mpr (fun address => by
      have scalarEquality := (innovationTreeShift_preserving rule p positive belowOne fixedPoint address).quasiMeasurePreserving.ae_eq_comp
        (Lp.coeFn_smul amplitude value)
      filter_upwards [scalarEquality] with marks sampleScalar
      simpa only [Function.comp_def, Pi.smul_apply, smul_eq_mul, chemicalField] using sampleScalar)
  filter_upwards [shiftedConvergence, shiftedScalars,
    chemicalOrbit_shift_eq_terminalScaledDistance_ae rule classical p positive belowOne fixedPoint growth growthPositive]
    with marks limits scalars distances
  intro address
  have shiftedLimit := (limits address).comp (tendsto_add_atTop_nat 1)
  simpa only [Function.comp_def, distances address, scalars address] using shiftedLimit

theorem chemical_terminal_field_lp_convergence_of_orbit_convergence
    (rule : Rule) (classical : rule.Classical)
    (p : ℝ) (positive : 0 < p) (belowOne : p < 1)
    (fixedPoint : rule.network.reliability p = p) (growth : ℝ) (growthPositive : 0 < growth)
    (value : Lp ℝ 2 (independentInnovationLaw rule p positive belowOne fixedPoint)) (amplitude : ℝ)
    (order : ℝ≥0∞)
    (convergence : Tendsto (fun depth => eLpNorm
      (⇑(chemicalOrbit rule p positive belowOne fixedPoint growth depth) - ⇑(amplitude • value))
      order (independentInnovationLaw rule p positive belowOne fixedPoint)) atTop (𝓝 0))
    (address : List (Fin rule.edges)) :
    Tendsto (fun depth => eLpNorm
      (fun marks => (markedTerminalDistance rule marks depth address true : ℝ) / growth ^ (depth + 1) -
        amplitude * chemicalField rule p positive belowOne fixedPoint value address marks)
      order (independentInnovationLaw rule p positive belowOne fixedPoint)) atTop (𝓝 0) := by
  have preserving := innovationTreeShift_preserving rule p positive belowOne fixedPoint address
  have scalarEquality := preserving.quasiMeasurePreserving.ae_eq_comp (Lp.coeFn_smul amplitude value)
  have distances := chemicalOrbit_shift_eq_terminalScaledDistance_ae rule classical p positive belowOne fixedPoint growth growthPositive
  have normEquality (depth : ℕ) : eLpNorm
      (fun marks => (markedTerminalDistance rule marks depth address true : ℝ) / growth ^ (depth + 1) -
        amplitude * chemicalField rule p positive belowOne fixedPoint value address marks)
        order (independentInnovationLaw rule p positive belowOne fixedPoint) =
      eLpNorm (⇑(chemicalOrbit rule p positive belowOne fixedPoint growth (depth + 1)) - ⇑(amplitude • value))
        order (independentInnovationLaw rule p positive belowOne fixedPoint) := by
    have equality : (fun marks => (markedTerminalDistance rule marks depth address true : ℝ) / growth ^ (depth + 1) -
        amplitude * chemicalField rule p positive belowOne fixedPoint value address marks) =ᵐ[
          independentInnovationLaw rule p positive belowOne fixedPoint]
        (⇑(chemicalOrbit rule p positive belowOne fixedPoint growth (depth + 1)) - ⇑(amplitude • value)) ∘
          innovationTreeShift rule address := by
      filter_upwards [distances, scalarEquality] with marks sampleDistances sampleScalar
      simp only [Function.comp_def, Pi.smul_apply, smul_eq_mul] at sampleScalar
      simp only [Function.comp_def, Pi.sub_apply, sampleDistances address depth, sampleScalar,
        Pi.smul_apply, smul_eq_mul, chemicalField]
    rw [eLpNorm_congr_ae equality]
    exact eLpNorm_comp_measurePreserving
      (p := order)
      (g := ⇑(chemicalOrbit rule p positive belowOne fixedPoint growth (depth + 1)) - ⇑(amplitude • value))
      (f := innovationTreeShift rule address)
      ((Lp.aestronglyMeasurable _).sub (Lp.aestronglyMeasurable _)) preserving
  simpa only [normEquality, Function.comp_def] using convergence.comp (tendsto_add_atTop_nat 1)

end IGSIII.Chemical.Substitution
