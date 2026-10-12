import IGSIII34.Spectral.ActualPositiveParameterResolvent20261011
import IGSIII34.ResistanceLimit.ActualComponentIntrinsicEnergyBridge
import IGSIII34.Diffusion.ActualElectricalComponentInjectivity

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2800000

namespace IGSIII34.Spectral
noncomputable section
open Universality Universality.FiniteNetwork IGSIII34.Percolation IGSIII34.ResistanceLimit
open IGSIII34.Diffusion IGSIII34.Forms IGSIII.Chemical.Substitution IGSIII.Geometry
open MeasureTheory Filter InnerProductSpace
open scoped _root_.Topology BoundedContinuousFunction

variable (rule : Rule) (p : ℝ) (positive : 0 < p) (belowOne : p < 1)
  (fixedPoint : rule.network.reliability p = p) (growth : ℝ)
  (value : Lp ℝ 2 (independentInnovationLaw rule p positive belowOne fixedPoint))
  (growthPositive : 0 < growth)
  (marks : {marks // ComponentElectricalTypical rule p positive belowOne fixedPoint growth value marks})
  (energyTypical : StationaryEnergyTypical rule p positive belowOne fixedPoint growth value marks.val)
  (anchor : ActualStationaryEnergySkeleton rule p positive belowOne fixedPoint growth value growthPositive
    (actualComponentEnergyMarks rule p positive belowOne fixedPoint growth value marks energyTypical))
  [CompactSpace (UniformSpace.Completion (ActualStationaryEnergySkeleton rule p positive belowOne fixedPoint growth value growthPositive
    (actualComponentEnergyMarks rule p positive belowOne fixedPoint growth value marks energyTypical)))]

local instance actualIntrinsicResolventNormCompletion20261011 :
    NormedAddCommGroup (actualAnchoredEnergyDomainCompletion20261011 rule p positive belowOne fixedPoint growth value growthPositive
      (actualComponentEnergyMarks rule p positive belowOne fixedPoint growth value marks energyTypical) anchor) :=
  actualAnchoredNormedAddCommGroup rule p positive belowOne fixedPoint growth value growthPositive
    (actualComponentEnergyMarks rule p positive belowOne fixedPoint growth value marks energyTypical) anchor
local instance actualIntrinsicResolventUniformCompletion20261011 :
    UniformSpace (actualAnchoredEnergyDomainCompletion20261011 rule p positive belowOne fixedPoint growth value growthPositive
      (actualComponentEnergyMarks rule p positive belowOne fixedPoint growth value marks energyTypical) anchor) :=
  (actualAnchoredNormedAddCommGroup rule p positive belowOne fixedPoint growth value growthPositive
    (actualComponentEnergyMarks rule p positive belowOne fixedPoint growth value marks energyTypical) anchor).toMetricSpace.toUniformSpace
local instance actualIntrinsicResolventTopologyCompletion20261011 :
    TopologicalSpace (actualAnchoredEnergyDomainCompletion20261011 rule p positive belowOne fixedPoint growth value growthPositive
      (actualComponentEnergyMarks rule p positive belowOne fixedPoint growth value marks energyTypical) anchor) :=
  (actualAnchoredNormedAddCommGroup rule p positive belowOne fixedPoint growth value growthPositive
    (actualComponentEnergyMarks rule p positive belowOne fixedPoint growth value marks energyTypical) anchor).toMetricSpace.toUniformSpace.toTopologicalSpace
local instance actualIntrinsicResolventInnerCompletion20261011 :
    InnerProductSpace ℝ (actualAnchoredEnergyDomainCompletion20261011 rule p positive belowOne fixedPoint growth value growthPositive
      (actualComponentEnergyMarks rule p positive belowOne fixedPoint growth value marks energyTypical) anchor) :=
  actualAnchoredInnerProductSpace rule p positive belowOne fixedPoint growth value growthPositive
    (actualComponentEnergyMarks rule p positive belowOne fixedPoint growth value marks energyTypical) anchor
local instance actualIntrinsicResolventCompleteCompletion20261011 :
    CompleteSpace (actualAnchoredEnergyDomainCompletion20261011 rule p positive belowOne fixedPoint growth value growthPositive
      (actualComponentEnergyMarks rule p positive belowOne fixedPoint growth value marks energyTypical) anchor) :=
  actual_anchored_completeSpace rule p positive belowOne fixedPoint growth value growthPositive
    (actualComponentEnergyMarks rule p positive belowOne fixedPoint growth value marks energyTypical) anchor

variable [MeasurableSpace (UniformSpace.Completion (ActualStationaryEnergySkeleton rule p positive belowOne fixedPoint growth value growthPositive
    (actualComponentEnergyMarks rule p positive belowOne fixedPoint growth value marks energyTypical)))]
  [BorelSpace (UniformSpace.Completion (ActualStationaryEnergySkeleton rule p positive belowOne fixedPoint growth value growthPositive
    (actualComponentEnergyMarks rule p positive belowOne fixedPoint growth value marks energyTypical)))]
  (measure : Measure (UniformSpace.Completion (ActualStationaryEnergySkeleton rule p positive belowOne fixedPoint growth value growthPositive
    (actualComponentEnergyMarks rule p positive belowOne fixedPoint growth value marks energyTypical))))
  [IsProbabilityMeasure measure] [measure.IsOpenPosMeasure]
  (data : ActualSpectralDataCompletion20261011 rule p positive belowOne fixedPoint growth value growthPositive
    (actualComponentEnergyMarks rule p positive belowOne fixedPoint growth value marks energyTypical) anchor measure)
  (coarse : ℕ) (word : Fin (coarse + 1) → Fin rule.edges × Bool)
  (live : retainedComponentState rule marks.val (List.ofFn word) ≠ .inactive)
  (stationary : ∀ address, electricalCell rule.network (marks.val (address, true))
    (fun edge => electricalField rule p positive belowOne fixedPoint value (address ++ [edge]) marks.val) =
      growth * electricalField rule p positive belowOne fixedPoint value address marks.val)

include stationary in
/-- The actual diagonal resolvent over the true selected component uses its
exact intrinsic completed diameter in root units. Its range is measurable
and its intrinsic completion compact by the proved closed embedding; no
diameter bound or local compactness conclusion is assumed. -/
theorem actual_positive_selected_component_intrinsic_resolvent_bound20261011
    (localPoint : ActualElectricalComponentSpace rule p positive belowOne fixedPoint growth value growthPositive marks (List.ofFn word))
    (parameter : ℝ) (parameterPositive : 0 < parameter)
    (massPositive : 0 < measure.real (Set.range
      (actualElectricalComponentCompletionInclusion rule p positive belowOne fixedPoint growth value growthPositive marks (List.ofFn word) live))) :
    diagonalLaplace (fun time => actualSpectralHeatKernelCompletion20261011 rule p positive belowOne fixedPoint growth value growthPositive
      (actualComponentEnergyMarks rule p positive belowOne fixedPoint growth value marks energyTypical) anchor measure data time
      (actualElectricalComponentCompletionInclusion rule p positive belowOne fixedPoint growth value growthPositive marks (List.ofFn word) live localPoint)
      (actualElectricalComponentCompletionInclusion rule p positive belowOne fixedPoint growth value growthPositive marks (List.ofFn word) live localPoint)) parameter ≤
      2 * max (1 / (parameter * measure.real (Set.range
        (actualElectricalComponentCompletionInclusion rule p positive belowOne fixedPoint growth value growthPositive marks (List.ofFn word) live))))
        (growth⁻¹ ^ (coarse + 1) * Metric.diam (Set.univ : Set
          (ActualElectricalComponentSpace rule p positive belowOne fixedPoint growth value growthPositive marks (List.ofFn word)))) := by
  letI : CompactSpace (ActualStationaryElectricalSpace rule p positive belowOne fixedPoint growth value growthPositive
      (componentTypicalRootElectricalMarks rule p positive belowOne fixedPoint growth value marks)) :=
    inferInstanceAs (CompactSpace (UniformSpace.Completion (ActualStationaryEnergySkeleton rule p positive belowOne fixedPoint growth value growthPositive
      (actualComponentEnergyMarks rule p positive belowOne fixedPoint growth value marks energyTypical))))
  have closedEmbedding := actualElectricalComponentCompletionInclusion_isClosedEmbedding rule p positive belowOne fixedPoint growth value
    growthPositive marks coarse word live stationary
  letI : CompactSpace (ActualElectricalComponentSpace rule p positive belowOne fixedPoint growth value growthPositive marks (List.ofFn word)) :=
    closedEmbedding.compactSpace
  have scalarNonnegative : 0 ≤ growth⁻¹ ^ (coarse + 1) := pow_nonneg (inv_nonneg.mpr growthPositive.le) _
  have diameterBound : ∀ other ∈ Set.range
      (actualElectricalComponentCompletionInclusion rule p positive belowOne fixedPoint growth value growthPositive marks (List.ofFn word) live),
      dist (actualElectricalComponentCompletionInclusion rule p positive belowOne fixedPoint growth value growthPositive marks (List.ofFn word) live localPoint) other ≤
        growth⁻¹ ^ (coarse + 1) * Metric.diam (Set.univ : Set
          (ActualElectricalComponentSpace rule p positive belowOne fixedPoint growth value growthPositive marks (List.ofFn word))) := by
    rintro other ⟨localOther, rfl⟩
    have includedBound := (actualElectricalComponentCompletionInclusion_lipschitz rule p positive belowOne fixedPoint growth value growthPositive
      marks (List.ofFn word) live).dist_le_mul localPoint localOther
    rw [Real.coe_toNNReal _ (pow_nonneg (inv_nonneg.mpr growthPositive.le) _)] at includedBound
    have length : (componentEdgeAddress (List.ofFn word)).length = coarse + 1 := by
      simp only [componentEdgeAddress, List.length_map, List.length_ofFn]
    rw [length] at includedBound
    exact includedBound.trans (mul_le_mul_of_nonneg_left
      (Metric.dist_le_diam_of_mem isCompact_univ.isBounded (Set.mem_univ localPoint) (Set.mem_univ localOther)) scalarNonnegative)
  have rangeClosed : IsClosed (Set.range
      (actualElectricalComponentCompletionInclusion rule p positive belowOne fixedPoint growth value growthPositive marks (List.ofFn word) live) :
      Set (UniformSpace.Completion (ActualStationaryEnergySkeleton rule p positive belowOne fixedPoint growth value growthPositive
        (actualComponentEnergyMarks rule p positive belowOne fixedPoint growth value marks energyTypical)))) :=
    actualElectricalComponentCompletionInclusion_closed_range rule p positive belowOne fixedPoint growth value growthPositive marks coarse word live stationary
  exact (actualSpectralData_positive_laplace_variational_completion20261011 rule p positive belowOne fixedPoint growth value growthPositive
      (actualComponentEnergyMarks rule p positive belowOne fixedPoint growth value marks energyTypical) anchor measure data
      (actualElectricalComponentCompletionInclusion rule p positive belowOne fixedPoint growth value growthPositive marks (List.ofFn word) live localPoint)
      parameter parameterPositive).trans_le
    (actual_completion_diagonal_local_upper_positive_completion20261011 rule p positive belowOne fixedPoint growth value growthPositive
      (actualComponentEnergyMarks rule p positive belowOne fixedPoint growth value marks energyTypical) measure parameter parameterPositive
      (actualElectricalComponentCompletionInclusion rule p positive belowOne fixedPoint growth value growthPositive marks (List.ofFn word) live localPoint)
      (Set.range (actualElectricalComponentCompletionInclusion rule p positive belowOne fixedPoint growth value growthPositive marks (List.ofFn word) live))
      rangeClosed.measurableSet
      (growth⁻¹ ^ (coarse + 1) * Metric.diam (Set.univ : Set
        (ActualElectricalComponentSpace rule p positive belowOne fixedPoint growth value growthPositive marks (List.ofFn word))))
      (mul_nonneg scalarNonnegative Metric.diam_nonneg) diameterBound massPositive)

/-- Generation zero is the whole original completed cluster. Its probability
mass is one and its exact intrinsic diameter is the global resistance diameter. -/
theorem actual_positive_whole_cluster_intrinsic_resolvent_bound20261011
    (point : UniformSpace.Completion (ActualStationaryEnergySkeleton rule p positive belowOne fixedPoint growth value growthPositive
      (actualComponentEnergyMarks rule p positive belowOne fixedPoint growth value marks energyTypical)))
    (parameter : ℝ) (parameterPositive : 0 < parameter) :
    diagonalLaplace (fun time => actualSpectralHeatKernelCompletion20261011 rule p positive belowOne fixedPoint growth value growthPositive
      (actualComponentEnergyMarks rule p positive belowOne fixedPoint growth value marks energyTypical) anchor measure data time point point) parameter ≤
      2 * max (1 / parameter) (Metric.diam (Set.univ : Set (UniformSpace.Completion
        (ActualStationaryEnergySkeleton rule p positive belowOne fixedPoint growth value growthPositive
          (actualComponentEnergyMarks rule p positive belowOne fixedPoint growth value marks energyTypical))))) := by
  have variationalBound := actual_completion_diagonal_local_upper_positive_completion20261011 rule p positive belowOne fixedPoint growth value growthPositive
    (actualComponentEnergyMarks rule p positive belowOne fixedPoint growth value marks energyTypical) measure parameter parameterPositive point
    Set.univ MeasurableSet.univ
    (Metric.diam (Set.univ : Set (UniformSpace.Completion (ActualStationaryEnergySkeleton rule p positive belowOne fixedPoint growth value growthPositive
      (actualComponentEnergyMarks rule p positive belowOne fixedPoint growth value marks energyTypical)))))
    Metric.diam_nonneg
    (fun other _ => Metric.dist_le_diam_of_mem isCompact_univ.isBounded (Set.mem_univ point) (Set.mem_univ other))
    (by simp)
  have laplaceBound := (actualSpectralData_positive_laplace_variational_completion20261011 rule p positive belowOne fixedPoint growth value growthPositive
    (actualComponentEnergyMarks rule p positive belowOne fixedPoint growth value marks energyTypical) anchor measure data point parameter parameterPositive).trans_le variationalBound
  simpa only [probReal_univ, mul_one] using laplaceBound

end
end IGSIII34.Spectral
