import Mathlib.MeasureTheory.Measure.LevyProkhorovMetric
import Mathlib.MeasureTheory.Measure.Portmanteau
import Mathlib.MeasureTheory.Constructions.BorelSpace.Metrizable
import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
import Mathlib.Probability.Kernel.Defs

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace IGSIII34.Diffusion
noncomputable section
open MeasureTheory ProbabilityTheory Filter TopologicalSpace
open scoped _root_.Topology ENNReal

variable {Environment Code : Type*} [MeasurableSpace Environment]
  [TopologicalSpace Code] [PseudoMetrizableSpace Code] [SeparableSpace Code]
  [MeasurableSpace Code] [BorelSpace Code]

/-- A weak-topology Borel measurable probability family is a genuine Giry
measurable family of measures. This conversion is proved, not assumed. -/
theorem weak_probability_to_measure_borel_measurable :
    @Measurable (ProbabilityMeasure Code) (Measure Code)
      (borel (ProbabilityMeasure Code)) inferInstance
      (fun probability => (probability : Measure Code)) := by
  letI : PseudoMetricSpace Code := pseudoMetrizableSpacePseudoMetric Code
  letI : MeasurableSpace (ProbabilityMeasure Code) := borel (ProbabilityMeasure Code)
  letI : BorelSpace (ProbabilityMeasure Code) := ⟨rfl⟩
  apply Measurable.measure_of_isPiSystem_of_isProbabilityMeasure
    (S := {set : Set Code | IsOpen set}) BorelSpace.measurable_eq isPiSystem_isOpen
  intro set openSet
  have lower : LowerSemicontinuous (fun probability : ProbabilityMeasure Code =>
      (probability : Measure Code) set) := by
    apply lowerSemicontinuous_iff_le_liminf.mpr
    intro probability
    exact ProbabilityMeasure.le_liminf_measure_open_of_tendsto
      (tendsto_id : Tendsto (fun probability : ProbabilityMeasure Code => probability)
        (𝓝 probability) (𝓝 probability)) openSet
  exact lower.measurable

/-- The a.e. weak limit of Borel measurable finite probability laws has a
measurable representative. No measurability of the proposed limit is input. -/
theorem exists_measurable_quenched_probability_limit
    (environmentLaw : Measure Environment)
    (sequence : ℕ → Environment → ProbabilityMeasure Code)
    (sequenceMeasurable : ∀ depth,
      @Measurable Environment (ProbabilityMeasure Code) inferInstance
        (borel (ProbabilityMeasure Code)) (sequence depth))
    (limit : Environment → ProbabilityMeasure Code)
    (convergence : ∀ᵐ environment ∂environmentLaw,
      Tendsto (fun depth => sequence depth environment) atTop (𝓝 (limit environment))) :
    ∃ measurableLimit : Environment → ProbabilityMeasure Code,
      @Measurable Environment (ProbabilityMeasure Code) inferInstance
        (borel (ProbabilityMeasure Code)) measurableLimit ∧
      measurableLimit =ᵐ[environmentLaw] limit ∧
      (∀ᵐ environment ∂environmentLaw,
        Tendsto (fun depth => sequence depth environment) atTop (𝓝 (measurableLimit environment))) := by
  letI : MeasurableSpace (ProbabilityMeasure Code) := borel (ProbabilityMeasure Code)
  letI : BorelSpace (ProbabilityMeasure Code) := ⟨rfl⟩
  have measurableLimit := aemeasurable_of_tendsto_metrizable_ae atTop
    (fun depth => (sequenceMeasurable depth).aemeasurable) convergence
  refine ⟨measurableLimit.mk limit, measurableLimit.measurable_mk,
    measurableLimit.ae_eq_mk.symm, ?_⟩
  filter_upwards [convergence, measurableLimit.ae_eq_mk] with environment converges equality
  rwa [← equality]

/-- The representative above yields an actual everywhere probability kernel,
equal a.e. to the specified quenched weak limit. -/
theorem exists_quenched_limit_markov_kernel
    (environmentLaw : Measure Environment)
    (sequence : ℕ → Environment → ProbabilityMeasure Code)
    (sequenceMeasurable : ∀ depth,
      @Measurable Environment (ProbabilityMeasure Code) inferInstance
        (borel (ProbabilityMeasure Code)) (sequence depth))
    (limit : Environment → ProbabilityMeasure Code)
    (convergence : ∀ᵐ environment ∂environmentLaw,
      Tendsto (fun depth => sequence depth environment) atTop (𝓝 (limit environment))) :
    ∃ kernel : Kernel Environment Code, ∃ kernelMarkov : IsMarkovKernel kernel,
      (∀ᵐ environment ∂environmentLaw, kernel environment = (limit environment : Measure Code)) ∧
      (∀ᵐ environment ∂environmentLaw,
        Tendsto (fun depth => sequence depth environment) atTop
          (𝓝 (⟨kernel environment, kernelMarkov.isProbabilityMeasure environment⟩ :
            ProbabilityMeasure Code))) := by
  obtain ⟨measurableLimit, measurableLimitMeasurable, equality, representativeConvergence⟩ :=
    exists_measurable_quenched_probability_limit environmentLaw sequence sequenceMeasurable limit convergence
  let kernel : Kernel Environment Code :=
    ⟨fun environment => (measurableLimit environment : Measure Code),
      weak_probability_to_measure_borel_measurable.comp measurableLimitMeasurable⟩
  have kernelMarkov : IsMarkovKernel kernel := ⟨fun environment => by
    change IsProbabilityMeasure (measurableLimit environment : Measure Code)
    infer_instance⟩
  letI : IsMarkovKernel kernel := kernelMarkov
  refine ⟨kernel, kernelMarkov, ?_, ?_⟩
  · filter_upwards [equality] with environment equality
    exact congrArg (fun probability : ProbabilityMeasure Code => (probability : Measure Code)) equality
  · exact representativeConvergence

end
end IGSIII34.Diffusion
