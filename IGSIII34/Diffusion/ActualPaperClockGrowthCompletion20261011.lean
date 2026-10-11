import IGSIII34.Diffusion.ActualDiscreteCountableLimitsCompletion20261011
import IGSIII34.Diffusion.ElectricalDegreeProjectionCompletion20261011
import Mathlib.Algebra.Order.Floor.Ring

set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option backward.isDefEq.respectTransparency false
namespace IGSIII34.Diffusion
noncomputable section
open Universality Universality.FiniteNetwork IGSIII34.ResistanceLimit IGSIII34.Percolation
open IGSIII.Chemical.Substitution IGSIII.Geometry MeasureTheory Filter ProbabilityTheory
open scoped _root_.Topology NNReal

variable (rule : Rule) (p : ℝ) (positive : 0 < p) (belowOne : p < 1)
  (fixedPoint : rule.network.reliability p = p) (growth : ℝ)
  (value : Lp ℝ 2 (independentInnovationLaw rule p positive belowOne fixedPoint))
  (growthPositive : 0 < growth)
  (marks : {marks // StationaryElectricalTypical rule p positive belowOne fixedPoint growth value marks})
  (chemicalScale : ℝ) (chemicalScalePositive : 0 < chemicalScale)

local instance actualClockGrowthMeasurableCompletion20261011 : MeasurableSpace
    (ActualStationaryElectricalSpace rule p positive belowOne fixedPoint growth value growthPositive marks) := borel _
local instance actualClockGrowthBorelCompletion20261011 : BorelSpace
    (ActualStationaryElectricalSpace rule p positive belowOne fixedPoint growth value growthPositive marks) := ⟨rfl⟩

include growthPositive

/-- Every real retained cluster has at least one edge, so the exact
manuscript clock dominates its true resistance growth factor. -/
theorem actualPaperDiscreteClock_lower_completion20261011 (depth : ℕ) :
    growth ^ (depth + 1) ≤ actualPaperDiscreteClockCompletion20261011 rule p positive belowOne fixedPoint growth value marks depth := by
  letI := clusterEdge_nonempty (rule.generation depth).network (stationaryConfiguration rule marks.val depth)
    (markedGenerationConfiguration_crosses rule marks.val marks.property.2.1 depth [] true)
  have cardPositive : 0 < (Fintype.card (ClusterEdge (rule.generation depth).network (stationaryConfiguration rule marks.val depth)) : ℝ) :=
    Nat.cast_pos.mpr Fintype.card_pos
  have cardLower : (1 : ℝ) ≤ Fintype.card (ClusterEdge (rule.generation depth).network (stationaryConfiguration rule marks.val depth)) := by
    exact_mod_cast Fintype.card_pos
  unfold actualPaperDiscreteClockCompletion20261011
  nlinarith [pow_pos growthPositive (depth + 1)]

theorem actualPaperDiscreteClock_positive_completion20261011 (depth : ℕ) :
    0 < actualPaperDiscreteClockCompletion20261011 rule p positive belowOne fixedPoint growth value marks depth :=
  (pow_pos growthPositive (depth + 1)).trans_le (actualPaperDiscreteClock_lower_completion20261011 rule p positive belowOne fixedPoint growth value growthPositive marks depth)

/-- The true paper clocks diverge on the same physical resistance-growth
regime already proved for the classical critical clusters. -/
theorem actualPaperDiscreteClock_diverges_completion20261011 (growthGreaterThanOne : 1 < growth) :
    Tendsto (actualPaperDiscreteClockCompletion20261011 rule p positive belowOne fixedPoint growth value marks) atTop atTop := by
  have growthDiverges : Tendsto (fun depth : ℕ => growth ^ (depth + 1)) atTop atTop :=
    (tendsto_pow_atTop_atTop_of_one_lt growthGreaterThanOne).comp (tendsto_add_atTop_nat 1)
  apply tendsto_atTop.mpr
  intro bound
  filter_upwards [growthDiverges.eventually (eventually_ge_atTop bound)] with depth large
  exact large.trans (actualPaperDiscreteClock_lower_completion20261011 rule p positive belowOne fixedPoint growth value growthPositive marks depth)

end
end IGSIII34.Diffusion

