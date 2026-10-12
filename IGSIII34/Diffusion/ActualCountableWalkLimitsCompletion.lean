import IGSIII34.Diffusion.CountableTimeLimitsCompletion
import IGSIII.Geometry.CriticalComponentGHP

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2600000

namespace IGSIII34.Diffusion
noncomputable section
open Universality Universality.FiniteNetwork IGSIII.Chemical.Substitution IGSIII.Geometry
open MeasureTheory MeasureTheory.Measure ProbabilityTheory Filter
open scoped Topology NNReal

variable (rule : Rule) (classicalRule : rule.Classical)
variable (configuration : ∀ depth, Configuration (rule.generation depth).edges)
variable (crossing : ∀ depth, (rule.generation depth).network.crosses (configuration depth) = true)
variable (coherent : configurationSequenceCoherent rule configuration)
variable (scale : ℝ) (scalePositive : 0 < scale)
variable (limitLength : ∀ coarse, Fin (rule.generation coarse).edges → ℝ)
variable (lengthNonnegative : ∀ depth edge, 0 ≤ limitLength depth edge)
variable (lengthPositive : ∀ depth edge, configuration depth edge = true → 0 < limitLength depth edge)
variable (childConvergence : ∀ coarse edge, Tendsto (fun fine =>
  (((rule.generation fine).network.openGraph
    (generationBlockCells rule coarse fine (configuration (coarse + fine + 1)) edge)).dist
      (rule.generation fine).network.source (rule.generation fine).network.target : ℝ) /
    scale ^ (coarse + fine + 2)) atTop (𝓝 (limitLength coarse edge)))

/-- The true entire-cluster natural degree-clock walk, started from the
actual degree probability rather than a presumed equilibrium law. -/
def actualStationaryNaturalDegreeWalkLaw (depth : ℕ) (resistance : ℝ≥0) :
    Measure (ℝ≥0 → ActualFiniteCluster rule configuration scale scalePositive depth) :=
  naturalDegreeWalkLaw (Vertex := ActualFiniteCluster rule configuration scale scalePositive depth)
    (clusterRetainedEndpoint (rule.generation depth).network (configuration depth))
    (cluster_degree_positive (rule.generation depth).network (configuration depth) (crossing depth))
    (actualFiniteClusterDegreeMeasure rule configuration crossing scale scalePositive depth)
    resistance depth

instance actualStationaryNaturalDegreeWalkLaw_probability (depth : ℕ) (resistance : ℝ≥0) :
    IsProbabilityMeasure (actualStationaryNaturalDegreeWalkLaw rule configuration crossing
      scale scalePositive depth resistance) := by
  unfold actualStationaryNaturalDegreeWalkLaw
  infer_instance

theorem actualStationaryNaturalDegreeWalkLaw_marginal (depth : ℕ)
    (resistance : ℝ≥0) (time : ℝ≥0) :
    (actualStationaryNaturalDegreeWalkLaw rule configuration crossing
      scale scalePositive depth resistance).map (fun path => path time) =
      actualFiniteClusterDegreeMeasure rule configuration crossing scale scalePositive depth := by
  letI := clusterEdge_nonempty (rule.generation depth).network (configuration depth) (crossing depth)
  exact naturalDegreeWalkLaw_degree_marginal _ _ _ _ _

variable [CompactSpace (ActualChemicalSpace rule classicalRule configuration coherent scale scalePositive
  limitLength lengthNonnegative lengthPositive childConvergence)]

local instance actualChemicalCarrierMeasurableCompletion :
    MeasurableSpace (ActualChemicalSpace rule classicalRule configuration coherent scale scalePositive
      limitLength lengthNonnegative lengthPositive childConvergence) := borel _

local instance actualChemicalCarrierBorelCompletion :
    BorelSpace (ActualChemicalSpace rule classicalRule configuration coherent scale scalePositive
      limitLength lengthNonnegative lengthPositive childConvergence) := ⟨rfl⟩

/-- A genuine probability on the countable observation skeleton, embedded
using the canonical actual born-vertex map into the same chemical completion
as Section 2. The underlying law is the full retained finite natural walk. -/
def actualChemicalStationaryDegreeObservationLaw (times : ℕ → ℝ≥0)
    (resistance : ℝ≥0) (depth : ℕ) :
    ProbabilityMeasure (ℕ → ActualChemicalSpace rule classicalRule configuration coherent scale scalePositive
      limitLength lengthNonnegative lengthPositive childConvergence) :=
  observedWalkProbabilityLaw
    (actualStationaryNaturalDegreeWalkLaw rule configuration crossing scale scalePositive depth resistance)
    times
    (fun vertex : ActualFiniteCluster rule configuration scale scalePositive depth =>
      actualChemicalVertex rule classicalRule configuration coherent scale scalePositive
        limitLength lengthNonnegative lengthPositive childConvergence depth vertex)
    (measurable_of_finite _)

theorem actualChemicalStationaryDegreeObservationLaw_marginal (times : ℕ → ℝ≥0)
    (resistance : ℝ≥0) (depth coordinate : ℕ) :
    ((actualChemicalStationaryDegreeObservationLaw rule classicalRule configuration crossing coherent
      scale scalePositive limitLength lengthNonnegative lengthPositive childConvergence times resistance depth).map
      (measurable_pi_apply coordinate).aemeasurable : Measure
        (ActualChemicalSpace rule classicalRule configuration coherent scale scalePositive
          limitLength lengthNonnegative lengthPositive childConvergence)) =
      (actualFiniteClusterDegreeMeasure rule configuration crossing scale scalePositive depth).map
        (fun vertex : ActualFiniteCluster rule configuration scale scalePositive depth =>
          actualChemicalVertex rule classicalRule configuration coherent scale scalePositive
            limitLength lengthNonnegative lengthPositive childConvergence depth vertex) := by
  rw [actualChemicalStationaryDegreeObservationLaw,
    observedWalkProbabilityLaw_marginal, actualStationaryNaturalDegreeWalkLaw_marginal]

/-- An actual-model subsequential limit on the entire countable observation
skeleton exists on every valid compact chemical carrier constructed in
Section 2. No limiting process, path convergence or kernel is an assumption. -/
theorem exists_actualChemicalStationaryDegreeObservationLaw_limit (times : ℕ → ℝ≥0)
    (resistance : ℝ≥0) :
    ∃ limitLaw : ProbabilityMeasure
        (ℕ → ActualChemicalSpace rule classicalRule configuration coherent scale scalePositive
          limitLength lengthNonnegative lengthPositive childConvergence),
      ∃ selectedDepth : ℕ → ℕ, StrictMono selectedDepth ∧
        Tendsto (fun index => actualChemicalStationaryDegreeObservationLaw rule classicalRule
          configuration crossing coherent scale scalePositive limitLength lengthNonnegative
          lengthPositive childConvergence times resistance (selectedDepth index)) atTop (𝓝 limitLaw) :=
  countableTimeLaws_subsequence_completion _

end
end IGSIII34.Diffusion
