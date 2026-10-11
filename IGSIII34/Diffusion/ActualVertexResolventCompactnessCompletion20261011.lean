import IGSIII34.Diffusion.ActualSelectedUniformCompletion20261011
import IGSIII34.Diffusion.ActualPaperClockWalkCompletion20261011
import IGSIII34.Diffusion.FiniteVertexObjectiveCompletion20261011
import IGSIII34.Diffusion.ClusterSourceEnergyCompletion20261011

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option backward.isDefEq.respectTransparency false

namespace IGSIII34.Diffusion
noncomputable section
open Universality Universality.FiniteNetwork IGSIII34.ResistanceLimit IGSIII34.Percolation
open IGSIII.Chemical.Substitution IGSIII.Geometry IGSIII34.Forms MeasureTheory Filter
open scoped _root_.Topology

def actualVertexClockGraphResolventCompletion20261011 (rule : Rule)
    (configuration : ∀ depth, Configuration (rule.generation depth).edges)
    (crossing : ∀ depth, (rule.generation depth).network.crosses (configuration depth) = true)
    (chemicalScale : ℝ) (chemicalScalePositive : 0 < chemicalScale) (depth : ℕ)
    (growth : ℝ) (growthPositive : 0 < growth) (parameter : ℝ) (parameterPositive : 0 < parameter)
    (forcing : ActualFiniteCluster rule configuration chemicalScale chemicalScalePositive depth → ℝ) :
    ActualFiniteCluster rule configuration chemicalScale chemicalScalePositive depth → ℝ :=
  letI : Nonempty (ActualFiniteCluster rule configuration chemicalScale chemicalScalePositive depth) :=
    ⟨⟨(rule.generation depth).network.source, SimpleGraph.Reachable.refl _⟩⟩
  letI := clusterEdge_nonempty (rule.generation depth).network (configuration depth) (crossing depth)
  finiteVertexResolventCompletion20261011
    (Vertex := ActualFiniteCluster rule configuration chemicalScale chemicalScalePositive depth)
    (clusterRetainedEndpoint (rule.generation depth).network (configuration depth))
    parameter (growth ^ (depth+1)) parameterPositive (pow_pos growthPositive _).le forcing
variable (rule : Rule) (p : ℝ) (positive : 0 < p) (belowOne : p < 1)
  (fixedPoint : rule.network.reliability p = p) (growth : ℝ)
  (value : Lp ℝ 2 (independentInnovationLaw rule p positive belowOne fixedPoint))
  (growthPositive : 0 < growth)
  (marks : {marks // StationaryHarmonicTypical rule p positive belowOne fixedPoint growth value marks})
  (chemicalScale : ℝ) (chemicalScalePositive : 0 < chemicalScale)
  (parameter : ℝ) (parameterPositive : 0 < parameter)
  (forcing : ∀ depth, ActualFiniteCluster rule (stationaryConfiguration rule marks.val) chemicalScale chemicalScalePositive depth → ℝ)

def actualOriginalVertexClockResolventPotentialCompletion20261011 (depth : ℕ) : Fin (rule.generation depth).vertices → ℝ :=
  retainedPotentialExtensionCompletion20261011 (rule.generation depth).network (stationaryConfiguration rule marks.val depth)
    (actualVertexClockGraphResolventCompletion20261011 rule (stationaryConfiguration rule marks.val)
      (fun depth => markedGenerationConfiguration_crosses rule marks.val marks.property.1.1.2.1 depth [] true)
      chemicalScale chemicalScalePositive depth growth growthPositive parameter parameterPositive (forcing depth))

theorem actualOriginalVertexClockResolvent_voltage_bound_completion20261011
    (bound : ℝ) (boundNonnegative : 0 ≤ bound) (forcingBound : ∀ depth vertex, |forcing depth vertex| ≤ bound) :
    ∀ depth vertex, |actualOriginalVertexClockResolventPotentialCompletion20261011 rule p positive belowOne fixedPoint growth value growthPositive
      marks chemicalScale chemicalScalePositive parameter parameterPositive forcing depth vertex| ≤ bound / parameter := by
  intro depth vertex
  letI : Nonempty (ActualFiniteCluster rule (stationaryConfiguration rule marks.val) chemicalScale chemicalScalePositive depth) :=
    ⟨⟨(rule.generation depth).network.source, SimpleGraph.Reachable.refl _⟩⟩
  letI := clusterEdge_nonempty (rule.generation depth).network (stationaryConfiguration rule marks.val depth)
    (markedGenerationConfiguration_crosses rule marks.val marks.property.1.1.2.1 depth [] true)
  unfold actualOriginalVertexClockResolventPotentialCompletion20261011 retainedPotentialExtensionCompletion20261011
  split_ifs with retained
  · exact finiteVertexResolvent_supremum_bound_completion20261011
      (Vertex := ActualFiniteCluster rule (stationaryConfiguration rule marks.val) chemicalScale chemicalScalePositive depth)
      (clusterRetainedEndpoint (rule.generation depth).network (stationaryConfiguration rule marks.val depth))
      parameter (growth ^ (depth + 1))
      parameterPositive (by positivity) (forcing depth) bound (forcingBound depth) ⟨vertex, retained⟩
  · simp only [abs_zero]
    exact div_nonneg boundNonnegative parameterPositive.le

theorem actualOriginalVertexClockResolvent_energy_bound_completion20261011
    (bound : ℝ) (boundNonnegative : 0 ≤ bound) (forcingBound : ∀ depth vertex, |forcing depth vertex| ≤ bound) :
    ∀ depth, sourceComponentEnergy (network (rule.generation depth).network (stationaryConfiguration rule marks.val depth))
      (fun _ => (growth ^ (depth + 1))⁻¹)
      (actualOriginalVertexClockResolventPotentialCompletion20261011 rule p positive belowOne fixedPoint growth value growthPositive
        marks chemicalScale chemicalScalePositive parameter parameterPositive forcing depth) ≤ bound ^ 2 / parameter := by
  intro depth
  letI : Nonempty (ActualFiniteCluster rule (stationaryConfiguration rule marks.val) chemicalScale chemicalScalePositive depth) :=
    ⟨⟨(rule.generation depth).network.source, SimpleGraph.Reachable.refl _⟩⟩
  letI := clusterEdge_nonempty (rule.generation depth).network (stationaryConfiguration rule marks.val depth)
    (markedGenerationConfiguration_crosses rule marks.val marks.property.1.1.2.1 depth [] true)
  rw [sourceEnergy_constant_inverse_scale_completion20261011]
  unfold actualOriginalVertexClockResolventPotentialCompletion20261011
  rw [retainedPotentialExtension_energy_completion20261011]
  exact finiteVertexResolvent_scaled_energy_bound_completion20261011
    (Vertex := ActualFiniteCluster rule (stationaryConfiguration rule marks.val) chemicalScale chemicalScalePositive depth)
    (clusterRetainedEndpoint (rule.generation depth).network (stationaryConfiguration rule marks.val depth))
    parameter (growth ^ (depth + 1)) parameterPositive (pow_pos growthPositive _).le (forcing depth) bound boundNonnegative (forcingBound depth)

/-- Actual full-cluster resolvents with the exact manuscript clock have
selected genuine finite-energy limits and converge uniformly at all embedded
finite vertices. This compactness does not assume a limiting resolvent or process. -/
theorem actualOriginalVertexClockResolvent_uniform_subsequence_completion20261011
    [CompactSpace (ActualStationaryElectricalSpace rule p positive belowOne fixedPoint growth value growthPositive
      ⟨marks.val, marks.property.1.1⟩)]
    (stationary : ∀ address, electricalCell rule.network (marks.val (address, true))
      (fun edge => electricalField rule p positive belowOne fixedPoint value (address ++ [edge]) marks.val) =
        growth * electricalField rule p positive belowOne fixedPoint value address marks.val)
    (fieldLimit : ∀ address, Tendsto
      (fun depth => growth⁻¹ ^ depth * electricalIteration rule marks.val depth address) atTop
      (𝓝 (electricalField rule p positive belowOne fixedPoint value address marks.val)))
    (eta coefficient : ℝ) (start : ℕ) (etaNonnegative : 0 ≤ eta) (etaBelowOne : eta < 1)
    (coefficientNonnegative : 0 ≤ coefficient)
    (radiusBound : ∀ address opened depth, start ≤ address.length →
      markedElectricalRadius rule marks.val depth address opened / growth ^ (depth + 1 + address.length) ≤
        coefficient * eta ^ address.length)
    (bound : ℝ) (boundNonnegative : 0 ≤ bound) (forcingBound : ∀ depth vertex, |forcing depth vertex| ≤ bound) :
    ∃ candidate : actualEnergyDomain rule p positive belowOne fixedPoint growth value growthPositive
        (harmonicTypicalEnergyMarks rule p positive belowOne fixedPoint growth value marks),
      ∃ selected : ℕ → ℕ, StrictMono selected ∧
      ∃ limitEnergy : ℝ, limitEnergy ≤ bound ^ 2 / parameter ∧
      limitingEnergy (actualEnergyEndpoint rule p positive belowOne fixedPoint growth value growthPositive
          (harmonicTypicalEnergyMarks rule p positive belowOne fixedPoint growth value marks))
        (actualEnergyConductance rule p positive belowOne fixedPoint growth value
          (harmonicTypicalEnergyMarks rule p positive belowOne fixedPoint growth value marks)) candidate.val ≤ limitEnergy ∧
      Tendsto (fun index => sourceComponentEnergy (network (rule.generation (selected index)).network
          (stationaryConfiguration rule marks.val (selected index))) (fun _ => (growth ^ (selected index + 1))⁻¹)
        (actualOriginalVertexClockResolventPotentialCompletion20261011 rule p positive belowOne fixedPoint growth value growthPositive
          marks chemicalScale chemicalScalePositive parameter parameterPositive forcing (selected index))) atTop (𝓝 limitEnergy) ∧
      ∀ tolerance : ℝ, 0 < tolerance → ∀ᶠ index in atTop,
        ∀ vertex : RetainedSkeletonVertex (rule.generation (selected index)).network (stationaryConfiguration rule marks.val (selected index)),
          |actualOriginalVertexClockResolventPotentialCompletion20261011 rule p positive belowOne fixedPoint growth value growthPositive
              marks chemicalScale chemicalScalePositive parameter parameterPositive forcing (selected index) vertex.val -
            actualEnergyExtensionLinear rule p positive belowOne fixedPoint growth value growthPositive
              (harmonicTypicalEnergyMarks rule p positive belowOne fixedPoint growth value marks) candidate
              (actualStationaryElectricalVertex rule p positive belowOne fixedPoint growth value growthPositive
                ⟨marks.val, marks.property.1.1⟩ (selected index) vertex)| < tolerance := by
  let potentials := actualOriginalVertexClockResolventPotentialCompletion20261011 rule p positive belowOne fixedPoint growth value growthPositive
    marks chemicalScale chemicalScalePositive parameter parameterPositive forcing
  have voltageBound := actualOriginalVertexClockResolvent_voltage_bound_completion20261011 rule p positive belowOne fixedPoint growth value
    growthPositive marks chemicalScale chemicalScalePositive parameter parameterPositive forcing bound boundNonnegative forcingBound
  have energyBound := actualOriginalVertexClockResolvent_energy_bound_completion20261011 rule p positive belowOne fixedPoint growth value
    growthPositive marks chemicalScale chemicalScalePositive parameter parameterPositive forcing bound boundNonnegative forcingBound
  obtain ⟨candidate, selected, strict, limitEnergy, limitBound, energyConvergence, candidateBound, convergence⟩ :=
    actualOriginal_bounded_energy_subsequence_completion20261011 rule p positive belowOne fixedPoint growth value growthPositive
      marks stationary fieldLimit potentials (bound / parameter) (bound ^ 2 / parameter)
      (fun depth vertex _ => voltageBound depth vertex) energyBound
  refine ⟨candidate, selected, strict, limitEnergy, limitBound, candidateBound, energyConvergence, ?_⟩
  exact actualOriginal_selected_uniform_completion20261011 rule p positive belowOne fixedPoint growth value growthPositive marks
    fieldLimit eta coefficient start etaNonnegative etaBelowOne coefficientNonnegative radiusBound potentials (bound ^ 2 / parameter)
    (by positivity) energyBound candidate selected strict.tendsto_atTop convergence

end
end IGSIII34.Diffusion


