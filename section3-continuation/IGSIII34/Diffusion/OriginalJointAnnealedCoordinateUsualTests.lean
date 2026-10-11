import IGSIII34.Diffusion.OriginalJointAnnealedUsualTests
import IGSIII34.Diffusion.CompletedEnvironmentJointAttachment

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace IGSIII34.Diffusion
noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped Topology NNReal

variable {Environment Coordinate : Type*} [MeasurableSpace Environment]
  [MetricSpace Coordinate] [SecondCountableTopology Coordinate]
  [MeasurableSpace Coordinate] [BorelSpace Coordinate]

/-- Bounded measurable joint tests are allowed any environmental
dependence; their state sections obey the genuine usual coupled criterion. -/
theorem annealed_coordinate_original_joint_usual_tests_of_quenched
    (environmentLaw : Measure Environment) [IsProbabilityMeasure environmentLaw]
    (coordinate : Environment → Coordinate) (coordinateMeasurable : Measurable coordinate)
    (kernels : ℕ → Kernel Environment OriginalJointCompactSpace)
    [∀ depth, IsMarkovKernel (kernels depth)]
    (limit : Kernel Environment OriginalJointCompactSpace) [IsMarkovKernel limit]
    (quenched : ∀ᵐ environment ∂environmentLaw,
      Tendsto (fun depth => conditionalKernelProbability (kernels depth) environment) atTop
        (𝓝 (conditionalKernelProbability limit environment)))
    (regular : ∀ᵐ environment ∂environmentLaw,
      OriginalJointUsualTestRegular (conditionalKernelProbability limit environment))
    (test : Coordinate × OriginalJointCompactSpace → ℝ) (measurable : Measurable test)
    (bound : ℝ≥0) (bounded : ∀ point, ‖test point‖ ≤ bound)
    (usualContinuous : ∀ value, OriginalJointUsualSequentiallyContinuousTest
      (fun point => test (value, point))) :
    Tendsto (fun depth => ∫ point, test point ∂
      (coordinateStateKernel coordinate coordinateMeasurable (kernels depth) ∘ₘ environmentLaw)) atTop
      (𝓝 (∫ point, test point ∂
        (coordinateStateKernel coordinate coordinateMeasurable limit ∘ₘ environmentLaw))) := by
  have innerIdentity (kernel : Kernel Environment OriginalJointCompactSpace) [IsMarkovKernel kernel]
      (environment : Environment) :
      (∫ point, test point ∂coordinateStateKernel coordinate coordinateMeasurable kernel environment) =
        ∫ point, test (coordinate environment, point) ∂kernel environment := by
    change (∫ point, test point ∂
      (conditionalKernelProbability (coordinateStateKernel coordinate coordinateMeasurable kernel)
        environment : Measure _)) = _
    rw [coordinateStateKernel_probability]
    exact integral_map (measurable_const.prodMk measurable_id).aemeasurable
      measurable.aestronglyMeasurable
  have identity (kernel : Kernel Environment OriginalJointCompactSpace) [IsMarkovKernel kernel] :
      (∫ point, test point ∂(coordinateStateKernel coordinate coordinateMeasurable kernel ∘ₘ environmentLaw)) =
        ∫ environment, ∫ point, test (coordinate environment, point) ∂kernel environment ∂environmentLaw := by
    have composition :
        (∫ point, test point ∂(coordinateStateKernel coordinate coordinateMeasurable kernel ∘ₘ environmentLaw)) =
          ∫ environment, ∫ point, test point ∂
            coordinateStateKernel coordinate coordinateMeasurable kernel environment ∂environmentLaw :=
      ProbabilityTheory.Kernel.integral_comp (κ := Kernel.const Unit environmentLaw)
        (η := coordinateStateKernel coordinate coordinateMeasurable kernel) (a := ())
        ((integrable_const (bound : ℝ)).mono' measurable.aestronglyMeasurable
          (Eventually.of_forall bounded))
    rw [composition]
    simp_rw [innerIdentity]
  simp_rw [identity]
  apply tendsto_integral_of_dominated_convergence (fun _ => (bound : ℝ))
  · intro depth
    exact ((measurable.comp (coordinateMeasurable.prodMap measurable_id)).stronglyMeasurable.integral_kernel_prod_right'
      (κ := kernels depth)).aestronglyMeasurable
  · exact integrable_const _
  · intro depth
    exact Eventually.of_forall (fun environment => by
      simpa using norm_integral_le_of_norm_le_const (μ := kernels depth environment)
        (Eventually.of_forall (fun point => bounded (coordinate environment, point))))
  · filter_upwards [quenched, regular] with environment convergence testRegular
    exact probability_weak_integral_bounded_ae_continuous _ _ convergence
      (fun point => test (coordinate environment, point))
      (measurable.comp (measurable_const.prodMk measurable_id)) bound
      (fun point => by simpa only [Real.norm_eq_abs] using bounded (coordinate environment, point))
      (testRegular _ (usualContinuous (coordinate environment)))

end
end IGSIII34.Diffusion
