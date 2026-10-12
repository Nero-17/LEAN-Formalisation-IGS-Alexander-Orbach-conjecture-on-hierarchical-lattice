import IGSIII34.Spectral.Collars.ActualNaturalAnnealedOriginalJoint
import IGSIII34.Diffusion.CompletedEnvironmentCoordinateJoint

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace IGSIII34.ResistanceLimit
noncomputable section
open Universality Universality.FiniteNetwork IGSIII.Chemical.Substitution
open IGSIII34.Percolation IGSIII34.Spectral IGSIII34.Diffusion
open MeasureTheory ProbabilityTheory Filter
open scoped _root_.Topology NNReal

variable (rule : Rule) (p : ℝ) (positive : 0 < p) (belowOne : p < 1)
  (fixedPoint : rule.network.reliability p = p)
  (natural : NaturalResistanceCompletion rule p positive belowOne fixedPoint)
  {Coordinate : Type*} [MetricSpace Coordinate] [SecondCountableTopology Coordinate]
  [MeasurableSpace Coordinate] [BorelSpace Coordinate]

/-- Every measurable environmental observation is retained jointly with
the original geometry, masses, terminals and entire path. The proof uses
exactly the ONE kernel returned by the actual natural master wrapper. -/
theorem exists_actual_natural_annealed_original_coordinate_joint
    (coordinate : ((List (Fin rule.edges) × Bool) → Configuration rule.edges) → Coordinate)
    (coordinateMeasurable : Measurable coordinate)
    (classicalRule : rule.Classical)
    (times : ℕ → ℝ≥0) (timeZero : times 0 = 0) (dense : DenseRange times) :
    ∃ chemicalGrowth : ℝ, ∃ chemicalGrowthPositive : 0 < chemicalGrowth,
      ∀ initial : ∀ depth, ((List (Fin rule.edges) × Bool) → Configuration rule.edges) →
        Fin (rule.generation depth).vertices,
      ∀ initialMeasurable : ∀ depth, Measurable (initial depth),
      ActualAnnealedStartingConvergence rule p positive belowOne fixedPoint natural initial →
      ∃ kernel : Kernel (NullMeasurableSpace
        ((List (Fin rule.edges) × Bool) → Configuration rule.edges)
        (independentInnovationLaw rule p positive belowOne fixedPoint)) OriginalJointCompactSpace,
      ∃ markov : IsMarkovKernel kernel,
        (∀ᵐ marks ∂(independentInnovationLaw rule p positive belowOne fixedPoint).completion,
          OriginalJointUsualTestRegular (completedEnvironmentKernelProbability kernel markov marks)) ∧
        (∀ᵐ marks ∂(independentInnovationLaw rule p positive belowOne fixedPoint).completion,
          ∀ kind : Fin 3, Tendsto (fun depth => completedEnvironmentKernelProbability
            (completedEnvironmentKernel (independentInnovationLaw rule p positive belowOne fixedPoint)
              (actualNaturalOriginalJointEnvironmentKernel rule p positive belowOne fixedPoint natural
                chemicalGrowth chemicalGrowthPositive initial initialMeasurable kind depth)) inferInstance marks)
            atTop (𝓝 (completedEnvironmentKernelProbability kernel markov marks))) ∧
        ∀ kind : Fin 3,
          Tendsto (fun depth => annealedKernelProbability
            (independentInnovationLaw rule p positive belowOne fixedPoint)
            (coordinateStateKernel coordinate coordinateMeasurable
              (actualNaturalOriginalJointEnvironmentKernel rule p positive belowOne fixedPoint natural
                chemicalGrowth chemicalGrowthPositive initial initialMeasurable kind depth))) atTop
            (𝓝 (completedEnvironmentAnnealedLimitProbability
              (independentInnovationLaw rule p positive belowOne fixedPoint).completion
              (coordinateStateKernel (fun marks : NullMeasurableSpace
                  ((List (Fin rule.edges) × Bool) → Configuration rule.edges)
                  (independentInnovationLaw rule p positive belowOne fixedPoint) => coordinate marks)
                (coordinateMeasurable.comp (completedEnvironmentIdentity_measurable
                  (independentInnovationLaw rule p positive belowOne fixedPoint))) kernel)
              (by letI := markov; infer_instance))) ∧
          ∀ test : Coordinate × OriginalJointCompactSpace → ℝ, Measurable test →
            ∀ bound : ℝ≥0, (∀ point, ‖test point‖ ≤ bound) →
              (∀ value, OriginalJointUsualSequentiallyContinuousTest (fun point => test (value, point))) →
              Tendsto (fun depth => ∫ point, test point ∂(
                coordinateStateKernel coordinate coordinateMeasurable
                  (actualNaturalOriginalJointEnvironmentKernel rule p positive belowOne fixedPoint natural
                    chemicalGrowth chemicalGrowthPositive initial initialMeasurable kind depth) ∘ₘ
                  independentInnovationLaw rule p positive belowOne fixedPoint)) atTop
                (𝓝 (∫ point, test point ∂(
                  coordinateStateKernel (fun marks : NullMeasurableSpace
                      ((List (Fin rule.edges) × Bool) → Configuration rule.edges)
                      (independentInnovationLaw rule p positive belowOne fixedPoint) => coordinate marks)
                    (coordinateMeasurable.comp (completedEnvironmentIdentity_measurable
                      (independentInnovationLaw rule p positive belowOne fixedPoint))) kernel ∘ₘ
                    (independentInnovationLaw rule p positive belowOne fixedPoint).completion))) := by
  obtain ⟨chemicalGrowth, chemicalGrowthPositive, actual⟩ :=
    exists_actual_natural_annealed_original_joint rule p positive belowOne fixedPoint natural
      classicalRule times timeZero dense
  refine ⟨chemicalGrowth, chemicalGrowthPositive, ?_⟩
  intro initial initialMeasurable starting
  obtain ⟨kernel, markov, regular, quenched, _⟩ := actual initial initialMeasurable starting
  letI := markov
  refine ⟨kernel, markov, regular, quenched, ?_⟩
  intro kind
  refine ⟨?_, ?_⟩
  · exact coordinate_joint_weak_of_completed_quenched
      (independentInnovationLaw rule p positive belowOne fixedPoint) coordinate coordinateMeasurable
      (actualNaturalOriginalJointEnvironmentKernel rule p positive belowOne fixedPoint natural
        chemicalGrowth chemicalGrowthPositive initial initialMeasurable kind) kernel
      (quenched.mono (fun _ convergence => convergence kind))
  · intro test measurable bound bounded usualContinuous
    exact coordinate_original_joint_usual_tests_of_completed_quenched
      (independentInnovationLaw rule p positive belowOne fixedPoint) coordinate coordinateMeasurable
      (actualNaturalOriginalJointEnvironmentKernel rule p positive belowOne fixedPoint natural
        chemicalGrowth chemicalGrowthPositive initial initialMeasurable kind) kernel
      (quenched.mono (fun _ convergence => convergence kind)) regular
      test measurable bound bounded usualContinuous

end
end IGSIII34.ResistanceLimit
