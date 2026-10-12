import IGSIII34.Spectral.Collars.ActualSameMasterOriginalJointExistence
import IGSIII34.Diffusion.CompletedEnvironmentOriginalJointFamily

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

/-- The three original natural-clock finite laws, before environmental
integration. Both masses, both terminals, the entire chemical carrier and
the entire original walk path occur in this genuine Markov kernel. -/
def actualNaturalOriginalJointEnvironmentKernel
    (chemicalGrowth : ℝ) (chemicalGrowthPositive : 0 < chemicalGrowth)
    (initial : ∀ depth, ((List (Fin rule.edges) × Bool) → Configuration rule.edges) →
      Fin (rule.generation depth).vertices)
    (initialMeasurable : ∀ depth, Measurable (initial depth))
    (kind : Fin 3) (depth : ℕ) :
    Kernel ((List (Fin rule.edges) × Bool) → Configuration rule.edges) OriginalJointCompactSpace :=
  actualFiniteOriginalJointEnvironmentKernel rule chemicalGrowth chemicalGrowthPositive depth
    (fun configuration => (actualFiniteAnnealedNaturalClock rule chemicalGrowth chemicalGrowthPositive
      depth natural.growth kind configuration : ℝ)) kind (initial depth) (initialMeasurable depth)

instance actualNaturalOriginalJointEnvironmentKernel_markov
    (chemicalGrowth : ℝ) (chemicalGrowthPositive : 0 < chemicalGrowth)
    (initial : ∀ depth, ((List (Fin rule.edges) × Bool) → Configuration rule.edges) →
      Fin (rule.generation depth).vertices)
    (initialMeasurable : ∀ depth, Measurable (initial depth))
    (kind : Fin 3) (depth : ℕ) :
    IsMarkovKernel (actualNaturalOriginalJointEnvironmentKernel rule p positive belowOne fixedPoint
      natural chemicalGrowth chemicalGrowthPositive initial initialMeasurable kind depth) := by
  unfold actualNaturalOriginalJointEnvironmentKernel
  infer_instance

/-- Genuine annealed marked-GHP/whole-path convergence on the ORIGINAL
common-isometric-coupling state space. All three original natural clocks
share ONE measurable completed-environment limit kernel. Its existence,
measurability and continuous-limit usual-J1 meaning are proved from the
actual master theorem, never assumed as input. -/
theorem exists_actual_natural_annealed_original_joint
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
            (actualNaturalOriginalJointEnvironmentKernel rule p positive belowOne fixedPoint natural
              chemicalGrowth chemicalGrowthPositive initial initialMeasurable kind depth)) atTop
            (𝓝 (completedEnvironmentAnnealedLimitProbability
              (independentInnovationLaw rule p positive belowOne fixedPoint).completion kernel markov)) ∧
          ∀ test : OriginalJointCompactSpace → ℝ, Measurable test →
            ∀ bound : ℝ≥0, (∀ point, ‖test point‖ ≤ bound) →
              OriginalJointUsualSequentiallyContinuousTest test →
              Tendsto (fun depth => ∫ point, test point ∂(
                actualNaturalOriginalJointEnvironmentKernel rule p positive belowOne fixedPoint natural
                  chemicalGrowth chemicalGrowthPositive initial initialMeasurable kind depth ∘ₘ
                  independentInnovationLaw rule p positive belowOne fixedPoint)) atTop
                (𝓝 (∫ point, test point ∂(kernel ∘ₘ
                  (independentInnovationLaw rule p positive belowOne fixedPoint).completion))) := by
  obtain ⟨chemicalGrowth, chemicalGrowthPositive, actual⟩ :=
    exists_ae_actual_natural_original_joint_limit rule p positive belowOne fixedPoint classicalRule natural
      times timeZero dense
  refine ⟨chemicalGrowth, chemicalGrowthPositive, ?_⟩
  intro initial initialMeasurable starting
  apply exists_completed_original_joint_annealed_family
    (independentInnovationLaw rule p positive belowOne fixedPoint) (0 : Fin 3)
    (actualNaturalOriginalJointEnvironmentKernel rule p positive belowOne fixedPoint natural
      chemicalGrowth chemicalGrowthPositive initial initialMeasurable)
  exact actual initial initialMeasurable starting

end
end IGSIII34.ResistanceLimit
