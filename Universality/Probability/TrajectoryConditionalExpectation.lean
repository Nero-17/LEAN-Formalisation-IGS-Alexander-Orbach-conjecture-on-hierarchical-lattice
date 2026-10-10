import Universality.Probability.MarkovTrajectory
import Mathlib.Probability.Martingale.Basic

namespace Universality
noncomputable section
open MeasureTheory ProbabilityTheory Preorder

variable {X : ℕ → Type*} [∀ n, MeasurableSpace (X n)]

/-- The conditional expectation given the entire past is the actual transition integral. -/
theorem markovTrajectory_condExp (initial : Measure (X 0)) [IsProbabilityMeasure initial]
    (transition : ∀ n, Kernel (X n) (X (n + 1)))
    [∀ n, IsMarkovKernel (transition n)] (n : ℕ)
    [StandardBorelSpace (X (n + 1))] [Nonempty (X (n + 1))]
    (observable : X (n + 1) → ℝ) (hmeas : StronglyMeasurable observable)
    (hint : Integrable (fun path => observable (path (n + 1))) (markovTrajectory initial transition)) :
    (markovTrajectory initial transition)[fun path => observable (path (n + 1)) | Filtration.piLE n]
      =ᵐ[markovTrajectory initial transition]
        fun path => ∫ next, observable next ∂transition n (path n) := by
  rw [Filtration.piLE_eq_comap_frestrictLe]
  have hcond := condExp_ae_eq_integral_condDistrib (measurable_frestrictLe n)
    (measurable_pi_apply (n + 1)).aemeasurable hmeas hint
  apply hcond.trans
  have hkernel := Kernel.condDistrib_trajMeasure
    (μ₀ := initial) (κ := pastKernel transition) (a := n)
  have hkernel' := ae_of_ae_map (measurable_frestrictLe n).aemeasurable hkernel
  filter_upwards [hkernel'] with path hpath
  exact congrArg (fun μ : Measure (X (n + 1)) => ∫ y, observable y ∂μ) hpath

end
end Universality
