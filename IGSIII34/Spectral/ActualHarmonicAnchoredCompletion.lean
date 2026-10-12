import IGSIII34.ResistanceLimit.ActualHarmonicDensity
import IGSIII34.Spectral.ActualCompactEmbeddingCompletion

/-! The actual coarse harmonic interpolants converge in the anchored
energy norm, hence uniformly on the compact electrical completion. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3600000
namespace IGSIII34.Spectral
noncomputable section
open Universality Universality.FiniteNetwork IGSIII34.Percolation IGSIII34.ResistanceLimit IGSIII34.Forms
open IGSIII.Chemical.Substitution IGSIII.Geometry MeasureTheory Filter
open scoped _root_.Topology

variable (rule : Rule) (p : ℝ) (positive : 0 < p) (belowOne : p < 1)
  (fixedPoint : rule.network.reliability p = p) (growth : ℝ)
  (value : Lp ℝ 2 (independentInnovationLaw rule p positive belowOne fixedPoint))
  (growthPositive : 0 < growth)
  (marks : {marks // StationaryHarmonicTypical rule p positive belowOne fixedPoint growth value marks})
  (anchor : ActualStationaryEnergySkeleton rule p positive belowOne fixedPoint growth value growthPositive
    (harmonicTypicalEnergyMarks rule p positive belowOne fixedPoint growth value marks))
  [CompactSpace (UniformSpace.Completion (ActualStationaryEnergySkeleton rule p positive belowOne fixedPoint growth value growthPositive
    (harmonicTypicalEnergyMarks rule p positive belowOne fixedPoint growth value marks)))]

local instance actualHarmonicAnchoredNormCompletion : NormedAddCommGroup
    (actualAnchoredEnergyDomainCompletion rule p positive belowOne fixedPoint growth value growthPositive
      (harmonicTypicalEnergyMarks rule p positive belowOne fixedPoint growth value marks) anchor) :=
  actualAnchoredNormedAddCommGroup rule p positive belowOne fixedPoint growth value growthPositive
    (harmonicTypicalEnergyMarks rule p positive belowOne fixedPoint growth value marks) anchor
local instance actualHarmonicAnchoredUniformCompletion : UniformSpace
    (actualAnchoredEnergyDomainCompletion rule p positive belowOne fixedPoint growth value growthPositive
      (harmonicTypicalEnergyMarks rule p positive belowOne fixedPoint growth value marks) anchor) :=
  (actualHarmonicAnchoredNormCompletion rule p positive belowOne fixedPoint growth value growthPositive marks anchor).toMetricSpace.toUniformSpace
local instance actualHarmonicAnchoredTopologyCompletion : TopologicalSpace
    (actualAnchoredEnergyDomainCompletion rule p positive belowOne fixedPoint growth value growthPositive
      (harmonicTypicalEnergyMarks rule p positive belowOne fixedPoint growth value marks) anchor) :=
  (actualHarmonicAnchoredNormCompletion rule p positive belowOne fixedPoint growth value growthPositive marks anchor).toMetricSpace.toUniformSpace.toTopologicalSpace
local instance actualHarmonicAnchoredInnerCompletion : InnerProductSpace ℝ
    (actualAnchoredEnergyDomainCompletion rule p positive belowOne fixedPoint growth value growthPositive
      (harmonicTypicalEnergyMarks rule p positive belowOne fixedPoint growth value marks) anchor) :=
  actualAnchoredInnerProductSpace rule p positive belowOne fixedPoint growth value growthPositive
    (harmonicTypicalEnergyMarks rule p positive belowOne fixedPoint growth value marks) anchor

def actualAnchoredHarmonicInterpolationCompletion (depth : ℕ)
    (potential : actualAnchoredEnergyDomainCompletion rule p positive belowOne fixedPoint growth value growthPositive
      (harmonicTypicalEnergyMarks rule p positive belowOne fixedPoint growth value marks) anchor) :
    actualAnchoredEnergyDomainCompletion rule p positive belowOne fixedPoint growth value growthPositive
      (harmonicTypicalEnergyMarks rule p positive belowOne fixedPoint growth value marks) anchor :=
  ⟨actualHarmonicInterpolation rule p positive belowOne fixedPoint growth value growthPositive marks depth potential.val,
    actualHarmonicInterpolation_finite rule p positive belowOne fixedPoint growth value growthPositive marks depth potential.val⟩

theorem actual_harmonic_interpolation_anchored_square_bound_completion
    (potential : actualAnchoredEnergyDomainCompletion rule p positive belowOne fixedPoint growth value growthPositive
      (harmonicTypicalEnergyMarks rule p positive belowOne fixedPoint growth value marks) anchor) (depth : ℕ) :
    ‖potential - actualAnchoredHarmonicInterpolationCompletion rule p positive belowOne fixedPoint growth value growthPositive marks anchor depth potential‖ ^ 2 ≤
      (Metric.diam (Set.univ : Set (UniformSpace.Completion (ActualStationaryEnergySkeleton rule p positive belowOne fixedPoint growth value growthPositive
        (harmonicTypicalEnergyMarks rule p positive belowOne fixedPoint growth value marks)))) + 1) *
      limitingEnergy
        (actualEnergyEndpoint rule p positive belowOne fixedPoint growth value growthPositive
          (harmonicTypicalEnergyMarks rule p positive belowOne fixedPoint growth value marks))
        (actualEnergyConductance rule p positive belowOne fixedPoint growth value
          (harmonicTypicalEnergyMarks rule p positive belowOne fixedPoint growth value marks))
        (fun point => potential.val point - actualHarmonicInterpolation rule p positive belowOne fixedPoint growth value growthPositive marks depth potential.val point) := by
  let sourceVertex : RetainedSkeletonVertex (rule.generation depth).network (stationaryConfiguration rule marks.val depth) :=
    ⟨(rule.generation depth).network.source, SimpleGraph.Reachable.refl _⟩
  let sourcePoint := electricalSkeletonVertex rule (stationaryConfiguration rule marks.val)
    (typicalStationaryCoherent rule p positive belowOne fixedPoint growth value ⟨marks.val, marks.property.1.1⟩)
    (stationaryResistance rule p positive belowOne fixedPoint growth value marks.val)
    (typicalStationaryResistance_positive rule p positive belowOne fixedPoint growth value growthPositive ⟨marks.val, marks.property.1.1⟩)
    marks.property.1.1.2.2 depth sourceVertex
  have interpolatedBoundary : actualHarmonicInterpolation rule p positive belowOne fixedPoint growth value growthPositive marks depth potential.val sourcePoint =
      potential.val sourcePoint :=
    harmonicInterpolation_boundary rule (stationaryConfiguration rule marks.val)
      (typicalStationaryCoherent rule p positive belowOne fixedPoint growth value ⟨marks.val, marks.property.1.1⟩)
      (stationaryResistance rule p positive belowOne fixedPoint growth value marks.val)
      (typicalStationaryResistance_positive rule p positive belowOne fixedPoint growth value growthPositive ⟨marks.val, marks.property.1.1⟩)
      marks.property.1.1.2.2 marks.property.2 depth potential.val sourceVertex
  let residual := potential - actualAnchoredHarmonicInterpolationCompletion rule p positive belowOne fixedPoint growth value growthPositive marks anchor depth potential
  have zeroAtBoundary : residual.val sourcePoint = 0 := by
    change potential.val sourcePoint - actualHarmonicInterpolation rule p positive belowOne fixedPoint growth value growthPositive marks depth potential.val sourcePoint = 0
    rw [interpolatedBoundary, sub_self]
  have resistanceBound := actual_finite_energy_resistance_bound rule p positive belowOne fixedPoint growth value growthPositive
    (harmonicTypicalEnergyMarks rule p positive belowOne fixedPoint growth value marks) residual.val residual.property anchor sourcePoint
  rw [zeroAtBoundary, sub_zero] at resistanceBound
  have diameterBound : dist anchor sourcePoint ≤ Metric.diam (Set.univ : Set (UniformSpace.Completion
      (ActualStationaryEnergySkeleton rule p positive belowOne fixedPoint growth value growthPositive
        (harmonicTypicalEnergyMarks rule p positive belowOne fixedPoint growth value marks)))) := by
    exact (UniformSpace.Completion.coe_isometry.dist_eq anchor sourcePoint).symm.trans_le
      (Metric.dist_le_diam_of_mem isCompact_univ.isBounded (Set.mem_univ _) (Set.mem_univ _))
  have energyNonnegative := limitingEnergy_nonnegative
    (actualEnergyEndpoint rule p positive belowOne fixedPoint growth value growthPositive
      (harmonicTypicalEnergyMarks rule p positive belowOne fixedPoint growth value marks))
    (actualEnergyConductance rule p positive belowOne fixedPoint growth value
      (harmonicTypicalEnergyMarks rule p positive belowOne fixedPoint growth value marks))
    (actualEnergyConductance_nonnegative rule p positive belowOne fixedPoint growth value growthPositive
      (harmonicTypicalEnergyMarks rule p positive belowOne fixedPoint growth value marks)) (potential := residual.val) residual.property
  have square := actual_anchored_norm_square rule p positive belowOne fixedPoint growth value growthPositive
    (harmonicTypicalEnergyMarks rule p positive belowOne fixedPoint growth value marks) anchor residual
  change ‖residual‖ ^ 2 = _ at square
  change ‖residual‖ ^ 2 ≤
    (Metric.diam (Set.univ : Set (UniformSpace.Completion (ActualStationaryEnergySkeleton rule p positive belowOne fixedPoint growth value growthPositive
      (harmonicTypicalEnergyMarks rule p positive belowOne fixedPoint growth value marks)))) + 1) *
    limitingEnergy
      (actualEnergyEndpoint rule p positive belowOne fixedPoint growth value growthPositive
        (harmonicTypicalEnergyMarks rule p positive belowOne fixedPoint growth value marks))
      (actualEnergyConductance rule p positive belowOne fixedPoint growth value
        (harmonicTypicalEnergyMarks rule p positive belowOne fixedPoint growth value marks)) residual.val
  rw [square]
  have anchorBound := resistanceBound.trans (mul_le_mul_of_nonneg_right diameterBound energyNonnegative)
  nlinarith

theorem actual_harmonic_interpolation_anchored_tendsto_completion
    (potential : actualAnchoredEnergyDomainCompletion rule p positive belowOne fixedPoint growth value growthPositive
      (harmonicTypicalEnergyMarks rule p positive belowOne fixedPoint growth value marks) anchor) :
    Tendsto (fun depth => actualAnchoredHarmonicInterpolationCompletion rule p positive belowOne fixedPoint growth value growthPositive marks anchor depth potential)
      atTop (𝓝 potential) := by
  apply Metric.tendsto_nhds.mpr
  intro tolerance positiveTolerance
  have positiveBound : 0 < Metric.diam (Set.univ : Set (UniformSpace.Completion
      (ActualStationaryEnergySkeleton rule p positive belowOne fixedPoint growth value growthPositive
        (harmonicTypicalEnergyMarks rule p positive belowOne fixedPoint growth value marks)))) + 1 := by
    positivity
  have energyLimit := actual_harmonic_residual_energy_tendsto rule p positive belowOne fixedPoint growth value growthPositive marks potential
  filter_upwards [energyLimit.eventually (gt_mem_nhds (div_pos (sq_pos_of_pos positiveTolerance) positiveBound))] with depth energySmall
  have normBound := actual_harmonic_interpolation_anchored_square_bound_completion rule p positive belowOne fixedPoint growth value growthPositive marks anchor potential depth
  have smallProduct := (lt_div_iff₀ positiveBound).mp energySmall
  rw [dist_eq_norm, norm_sub_rev]
  nlinarith [norm_nonneg (potential - actualAnchoredHarmonicInterpolationCompletion rule p positive belowOne fixedPoint growth value growthPositive marks anchor depth potential)]

theorem actual_harmonic_interpolation_continuous_tendsto_completion
    (potential : actualAnchoredEnergyDomainCompletion rule p positive belowOne fixedPoint growth value growthPositive
      (harmonicTypicalEnergyMarks rule p positive belowOne fixedPoint growth value marks) anchor) :
    Tendsto (fun depth => actualEnergyContinuousEmbeddingCompletion rule p positive belowOne fixedPoint growth value growthPositive
      (harmonicTypicalEnergyMarks rule p positive belowOne fixedPoint growth value marks) anchor
      (actualAnchoredHarmonicInterpolationCompletion rule p positive belowOne fixedPoint growth value growthPositive marks anchor depth potential))
      atTop (𝓝 (actualEnergyContinuousEmbeddingCompletion rule p positive belowOne fixedPoint growth value growthPositive
        (harmonicTypicalEnergyMarks rule p positive belowOne fixedPoint growth value marks) anchor potential)) :=
  (actualEnergyContinuousEmbeddingCompletion rule p positive belowOne fixedPoint growth value growthPositive
    (harmonicTypicalEnergyMarks rule p positive belowOne fixedPoint growth value marks) anchor).continuous.tendsto potential |>.comp
    (actual_harmonic_interpolation_anchored_tendsto_completion rule p positive belowOne fixedPoint growth value growthPositive marks anchor potential)

end
end IGSIII34.Spectral
