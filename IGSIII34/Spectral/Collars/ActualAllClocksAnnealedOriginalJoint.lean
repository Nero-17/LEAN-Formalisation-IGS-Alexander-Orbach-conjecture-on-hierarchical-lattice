import IGSIII34.Spectral.Collars.ActualSameMasterAllClocksOriginalJointExistence
import IGSIII34.Spectral.Collars.ActualNaturalAnnealedOriginalJoint
import IGSIII34.Diffusion.CompletedEnvironmentOriginalJointCertificate

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

def actualDeterministicOriginalJointEnvironmentKernel
    (chemicalGrowth : ℝ) (chemicalGrowthPositive : 0 < chemicalGrowth)
    (initial : ∀ depth, ((List (Fin rule.edges) × Bool) → Configuration rule.edges) →
      Fin (rule.generation depth).vertices)
    (initialMeasurable : ∀ depth, Measurable (initial depth))
    (kind : Fin 3) (depth : ℕ) :
    Kernel ((List (Fin rule.edges) × Bool) → Configuration rule.edges) OriginalJointCompactSpace :=
  actualFiniteOriginalJointEnvironmentKernel rule chemicalGrowth chemicalGrowthPositive depth
    (fun _ => actualFiniteAnnealedDeterministicClock rule p natural.growth depth) kind
    (initial depth) (initialMeasurable depth)

instance actualDeterministicOriginalJointEnvironmentKernel_markov
    (chemicalGrowth : ℝ) (chemicalGrowthPositive : 0 < chemicalGrowth)
    (initial : ∀ depth, ((List (Fin rule.edges) × Bool) → Configuration rule.edges) →
      Fin (rule.generation depth).vertices)
    (initialMeasurable : ∀ depth, Measurable (initial depth))
    (kind : Fin 3) (depth : ℕ) :
    IsMarkovKernel (actualDeterministicOriginalJointEnvironmentKernel rule p positive belowOne fixedPoint
      natural chemicalGrowth chemicalGrowthPositive initial initialMeasurable kind depth) := by
  unfold actualDeterministicOriginalJointEnvironmentKernel
  infer_instance

/-- All original finite clocks have genuine annealed original joint limits
with ONE chemical normalization and arbitrary measurable convergent starts.
The natural clocks share one completed-environment Markov limit kernel;
deterministic discrete and rate-one clocks share another, and the inverse-degree
deterministic clock retains its corresponding continuous time change.
Every certificate includes original environmental annealed weak convergence
and all bounded measurable usual-local-J1 joint tests at the SAME limit kernel. -/
theorem exists_actual_all_clocks_annealed_original_joint
    (classicalRule : rule.Classical)
    (times : ℕ → ℝ≥0) (timeZero : times 0 = 0) (dense : DenseRange times) :
    ∃ chemicalGrowth : ℝ, ∃ chemicalGrowthPositive : 0 < chemicalGrowth,
      ∀ initial : ∀ depth, ((List (Fin rule.edges) × Bool) → Configuration rule.edges) →
        Fin (rule.generation depth).vertices,
      ∀ initialMeasurable : ∀ depth, Measurable (initial depth),
      ActualAnnealedStartingConvergence rule p positive belowOne fixedPoint natural initial →
      Nonempty (CompletedOriginalJointAnnealedFamilyCertificate
        (independentInnovationLaw rule p positive belowOne fixedPoint)
        (actualNaturalOriginalJointEnvironmentKernel rule p positive belowOne fixedPoint natural
          chemicalGrowth chemicalGrowthPositive initial initialMeasurable)) ∧
      Nonempty (CompletedOriginalJointAnnealedFamilyCertificate
        (independentInnovationLaw rule p positive belowOne fixedPoint)
        (fun index : Fin 2 => actualDeterministicOriginalJointEnvironmentKernel rule p positive belowOne fixedPoint natural
          chemicalGrowth chemicalGrowthPositive initial initialMeasurable (index.castLE (by decide : 2 ≤ 3)))) ∧
      Nonempty (CompletedOriginalJointAnnealedFamilyCertificate
        (independentInnovationLaw rule p positive belowOne fixedPoint)
        (fun _ : Fin 1 => actualDeterministicOriginalJointEnvironmentKernel rule p positive belowOne fixedPoint natural
          chemicalGrowth chemicalGrowthPositive initial initialMeasurable 2)) := by
  obtain ⟨chemicalGrowth, chemicalGrowthPositive, actual⟩ :=
    exists_ae_actual_all_clocks_original_joint_limits rule p positive belowOne fixedPoint classicalRule natural
      times timeZero dense
  refine ⟨chemicalGrowth, chemicalGrowthPositive, ?_⟩
  intro initial initialMeasurable starting
  have actualExistence := actual initial initialMeasurable starting
  refine ⟨?_, ?_, ?_⟩
  · apply exists_completed_original_joint_annealed_family_certificate
      (independentInnovationLaw rule p positive belowOne fixedPoint)
      (actualNaturalOriginalJointEnvironmentKernel rule p positive belowOne fixedPoint natural
        chemicalGrowth chemicalGrowthPositive initial initialMeasurable) (0 : Fin 3)
    filter_upwards [actualExistence] with marks existence
    rcases existence with ⟨target, regular, weak, deterministicLaws, same, deterministicRegular, deterministicWeak⟩
    exact ⟨target, regular, weak⟩
  · apply exists_completed_original_joint_annealed_family_certificate
      (independentInnovationLaw rule p positive belowOne fixedPoint)
      (fun index : Fin 2 => actualDeterministicOriginalJointEnvironmentKernel rule p positive belowOne fixedPoint natural
        chemicalGrowth chemicalGrowthPositive initial initialMeasurable (index.castLE (by decide : 2 ≤ 3))) (0 : Fin 2)
    filter_upwards [actualExistence] with marks existence
    rcases existence with ⟨target, regular, weak, deterministicLaws, same, deterministicRegular, deterministicWeak⟩
    refine ⟨deterministicLaws 0, deterministicRegular 0, ?_⟩
    intro index
    have targetIdentity : deterministicLaws (index.castLE (by decide : 2 ≤ 3)) = deterministicLaws 0 := by
      fin_cases index
      · rfl
      · exact same.symm
    have convergence := deterministicWeak (index.castLE (by decide : 2 ≤ 3))
    rw [targetIdentity] at convergence
    exact convergence
  · apply exists_completed_original_joint_annealed_family_certificate
      (independentInnovationLaw rule p positive belowOne fixedPoint)
      (fun _ : Fin 1 => actualDeterministicOriginalJointEnvironmentKernel rule p positive belowOne fixedPoint natural
        chemicalGrowth chemicalGrowthPositive initial initialMeasurable 2) (0 : Fin 1)
    filter_upwards [actualExistence] with marks existence
    rcases existence with ⟨target, regular, weak, deterministicLaws, same, deterministicRegular, deterministicWeak⟩
    exact ⟨deterministicLaws 2, deterministicRegular 2, fun _ => deterministicWeak 2⟩

end
end IGSIII34.ResistanceLimit
