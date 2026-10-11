import IGSIII34.Diffusion.ActualWeightedClockRescaleCompletion20261011
import IGSIII34.Diffusion.ActualVertexSpeedGlobalWeakCompletion20261011
import IGSIII34.Diffusion.ActualNaturalAdditiveClockCompletion20261011
import IGSIII34.Diffusion.ActualDiscreteGlobalWholeWeakCompletion20261011
import IGSIII34.Diffusion.ActualContinuousLimitAssemblyCompletion20261011
import IGSIII34.Diffusion.ActualNaturalDegreeMassCompletion20261011
import IGSIII34.Diffusion.ActualResolventUniformCompletion20261011
import IGSIII34.Spectral.ActualNaturalSpectralWitnessCompletion20261011

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4200000
namespace IGSIII34.Diffusion
noncomputable section
open Universality Universality.FiniteNetwork IGSIII34.Percolation IGSIII34.ResistanceLimit IGSIII34.Forms IGSIII34.Spectral
open IGSIII.Chemical.Substitution IGSIII.Geometry MeasureTheory Filter
open scoped _root_.Topology NNReal

local instance sameLimitNaturalClockRescaleCompletionMeasurableCompletion20261011 {Carrier : Type*} [UniformSpace Carrier] : MeasurableSpace (UniformSpace.Completion Carrier) := borel _
local instance sameLimitNaturalClockRescaleCompletionBorelCompletion20261011 {Carrier : Type*} [UniformSpace Carrier] : BorelSpace (UniformSpace.Completion Carrier) := ⟨rfl⟩

/-- The original natural field supplies all electrical convergence and mesh
inputs. Any actual Perron boundary realization with the same vertex ratios
therefore has whole finite-resolvent convergence on the genuine paper clock. -/
local instance sameLimitNaturalClockRescaleContinuousMeasurableCompletion20261011 {Space : Type*} [TopologicalSpace Space] : MeasurableSpace C(ℝ≥0, Space) := borel _
local instance sameLimitNaturalClockRescaleContinuousBorelCompletion20261011 {Space : Type*} [TopologicalSpace Space] : BorelSpace C(ℝ≥0, Space) := ⟨rfl⟩
local instance sameLimitNaturalClockRescaleCarrierMeasurableCompletion20261011 (rule : Rule) (p : ℝ) (positive : 0 < p) (belowOne : p < 1)
    (fixedPoint : rule.network.reliability p = p) (growth : ℝ)
    (value : Lp ℝ 2 (independentInnovationLaw rule p positive belowOne fixedPoint))
    (growthPositive : 0 < growth)
    (marks : {marks // StationaryElectricalTypical rule p positive belowOne fixedPoint growth value marks}) :
    MeasurableSpace (ActualStationaryElectricalSpace rule p positive belowOne fixedPoint growth value growthPositive marks) := borel _
local instance sameLimitNaturalClockRescaleCarrierBorelCompletion20261011 (rule : Rule) (p : ℝ) (positive : 0 < p) (belowOne : p < 1)
    (fixedPoint : rule.network.reliability p = p) (growth : ℝ)
    (value : Lp ℝ 2 (independentInnovationLaw rule p positive belowOne fixedPoint))
    (growthPositive : 0 < growth)
    (marks : {marks // StationaryElectricalTypical rule p positive belowOne fixedPoint growth value marks}) :
    BorelSpace (ActualStationaryElectricalSpace rule p positive belowOne fixedPoint growth value growthPositive marks) := ⟨rfl⟩
theorem ae_actual_natural_weighted_clock_rescale_same_limit
    (rule : Rule) (classicalRule : rule.Classical) (p : ℝ)
    (positive : 0 < p) (belowOne : p < 1) (fixedPoint : rule.network.reliability p = p)
    (natural : NaturalResistanceCompletion20261011 rule p positive belowOne fixedPoint)
    (weight : List (Fin rule.edges × Bool) → (((List (Fin rule.edges) × Bool) → Configuration rule.edges) → ℝ))
    (actualRatios : ∀ᵐ marks ∂independentInnovationLaw rule p positive belowOne fixedPoint,
      ∀ address, Tendsto (fun depth =>
        markedOrientedVertexMass rule marks depth (componentEdgeAddress address) (retainedComponentState rule marks address) /
          markedOrientedVertexMass rule marks (depth + address.length) [] .connected)
        atTop (𝓝 (weight address marks)))
    (nonnegative : ∀ᵐ marks ∂independentInnovationLaw rule p positive belowOne fixedPoint,
      ∀ address, 0 ≤ weight address marks) :
    ∀ᵐ marks ∂independentInnovationLaw rule p positive belowOne fixedPoint,
      ∀ typical : StationaryHarmonicTypical rule p positive belowOne fixedPoint natural.growth (natural.amplitude • natural.field) marks,
      ∀ compactness : CompactSpace (UniformSpace.Completion (ActualStationaryEnergySkeleton rule p positive belowOne fixedPoint natural.growth (natural.amplitude • natural.field) (zero_lt_one.trans natural.aboveOne) (harmonicTypicalEnergyMarks rule p positive belowOne fixedPoint natural.growth (natural.amplitude • natural.field) ⟨marks, typical⟩))),
      letI := compactness
      letI : CompactSpace (ActualStationaryElectricalSpace rule p positive belowOne fixedPoint natural.growth (natural.amplitude • natural.field)
        (zero_lt_one.trans natural.aboveOne) ⟨marks, typical.1.1⟩) := compactness
      ∀ (boundary : Measure (Π depth, Fin depth → (Fin rule.edges × Bool)))
        (probability : IsProbabilityMeasure boundary)
        (atoms : ∀ age word, boundary {path | path age = word} = ENNReal.ofReal (weight (List.ofFn word) marks)),
      ∀ realization : (Π depth, Fin depth → (Fin rule.edges × Bool)) → ActualStationaryElectricalSpace rule p positive belowOne fixedPoint natural.growth (natural.amplitude • natural.field) (zero_lt_one.trans natural.aboveOne) ⟨marks, typical.1.1⟩,
      Tendsto (fun depth => levyProkhorovEDist
        (boundary.map (fun path => actualElectricalComponentWordPoint rule p positive belowOne fixedPoint natural.growth (natural.amplitude • natural.field) (zero_lt_one.trans natural.aboveOne) marks typical.1.1 depth (path (depth + 1))))
        (boundary.map realization)) atTop (𝓝 0) →
      ∀ massProbability : IsProbabilityMeasure (boundary.map realization),
      ∀ massOpenPositive : (boundary.map realization).IsOpenPosMeasure,
      letI := massProbability
      letI := massOpenPositive
      ∀ (chemicalScale : ℝ) (chemicalScalePositive : 0 < chemicalScale),
      ∀ anchor : ActualStationaryEnergySkeleton rule p positive belowOne fixedPoint natural.growth (natural.amplitude • natural.field) (zero_lt_one.trans natural.aboveOne) (harmonicTypicalEnergyMarks rule p positive belowOne fixedPoint natural.growth (natural.amplitude • natural.field) ⟨marks, typical⟩),
      ∀ data : ActualSpectralDataCompletion20261011 rule p positive belowOne fixedPoint natural.growth (natural.amplitude • natural.field)
        (zero_lt_one.trans natural.aboveOne)
        (harmonicTypicalEnergyMarks rule p positive belowOne fixedPoint natural.growth (natural.amplitude • natural.field) ⟨marks, typical⟩) anchor (boundary.map realization),
      ∀ initial : ∀ depth, ProbabilityMeasure (ActualFiniteCluster rule (stationaryConfiguration rule marks) chemicalScale chemicalScalePositive depth),
      ∀ (times : ℕ → ℝ≥0) (timeZero : times 0 = 0) (dense : DenseRange times),
      ∀ limitLaw : ProbabilityMeasure (ℕ → ActualStationaryElectricalSpace rule p positive belowOne fixedPoint natural.growth (natural.amplitude • natural.field)
        (zero_lt_one.trans natural.aboveOne) ⟨marks, typical.1.1⟩),

      Tendsto (fun depth => actualPaperDiscreteElectricalObservationLawCompletion20261011 rule p positive belowOne fixedPoint
        natural.growth (natural.amplitude • natural.field) (zero_lt_one.trans natural.aboveOne) ⟨marks, typical.1.1⟩
        chemicalScale chemicalScalePositive times initial depth) atTop (𝓝 limitLaw) →

      ∀ countingSpeed : Bool,
      ∀ (ratios : ℕ → ℝ≥0) (ratiosPositive : ∀ depth, 0 < ratios depth),
      ∀ (ratio : ℝ≥0) (ratioPositive : 0 < ratio),
      Tendsto ratios atTop (𝓝 ratio) →
        Tendsto (fun depth => actualWeightedClockRescaledGlobalLawCompletion20261011 rule p positive belowOne fixedPoint
          natural.growth (natural.amplitude • natural.field) (zero_lt_one.trans natural.aboveOne) ⟨marks, typical⟩
          chemicalScale chemicalScalePositive countingSpeed ratios ratiosPositive depth (initial depth)) atTop
          (𝓝 (limitLaw.map (continuousGlobalFamily_measurable_completion20261011
            (fun path time => countableTimeContinuousSampleCompletion20261011 times dense path (ratio*time))
            (fun path => (countableTimeContinuousSample_continuous_completion20261011 times dense path).comp (continuous_const.mul continuous_id))
            (fun time => countableTimeContinuousSample_evaluation_measurable_completion20261011 times dense (ratio*time))).aemeasurable)) := by
  obtain ⟨constant, constantPositive, growthBounds, membership, endpointFixed⟩ :=
    natural_physical_omega_witness_completion20261011 rule classicalRule p positive belowOne fixedPoint natural
  have growthPositive := zero_lt_one.trans natural.aboveOne
  have physicalPositive : ∀ᵐ marks ∂independentInnovationLaw rule p positive belowOne fixedPoint,
      0 < (natural.amplitude • natural.field) marks := by
    filter_upwards [Lp.coeFn_smul natural.amplitude natural.field, natural.fieldPositive] with marks scalar fieldPositive
    rw [scalar]
    simp only [Pi.smul_apply, smul_eq_mul]
    exact mul_pos (zero_lt_one.trans_le natural.amplitudeLower) fieldPositive
  obtain ⟨eta, inverseBelowEta, etaBelowOne⟩ := exists_between (inv_lt_one_of_one_lt₀ natural.aboveOne)
  have etaPositive := (inv_pos.mpr growthPositive).trans inverseBelowEta
  have productGreaterThanOne : 1 < natural.growth * eta := by
    have multiplied := mul_lt_mul_of_pos_left inverseBelowEta growthPositive
    simpa only [mul_inv_cancel₀ growthPositive.ne'] using multiplied
  filter_upwards [ae_actual_natural_additive_clock_prefix_probability_tendsto_completion20261011 rule classicalRule p positive belowOne fixedPoint natural weight actualRatios nonnegative,
    ae_actualCountingClock_density_bound_completion20261011 rule classicalRule p positive belowOne fixedPoint,
    ae_actual_natural_degree_mass_tendsto_completion20261011 rule classicalRule p positive belowOne fixedPoint natural weight actualRatios nonnegative,
    electricalField_stationary_of_fixed rule p positive belowOne fixedPoint natural.growth growthPositive (natural.amplitude • natural.field) physicalPositive endpointFixed,
    actual_electrical_field_limits_fixed_cluster rule classicalRule p positive belowOne fixedPoint constant natural.growth constantPositive growthPositive
      growthBounds (natural.amplitude • natural.field) endpointFixed membership,
    ae_uniform_actual_electrical_mesh_fixed_cluster rule classicalRule p positive belowOne fixedPoint constant natural.growth constantPositive natural.aboveOne
      growthBounds (natural.amplitude • natural.field) endpointFixed membership eta etaPositive etaBelowOne productGreaterThanOne]
    with marks centered density degrees stationary fields mesh
  obtain ⟨start, radiusBounds⟩ := mesh
  intro typical compactness
  letI := compactness
  letI : CompactSpace (ActualStationaryElectricalSpace rule p positive belowOne fixedPoint natural.growth (natural.amplitude • natural.field)
    (zero_lt_one.trans natural.aboveOne) ⟨marks, typical.1.1⟩) := compactness
  intro boundary probability atoms realization projection massProbability massOpenPositive
  letI := probability
  letI := massProbability
  letI := massOpenPositive
  intro chemicalScale chemicalScalePositive anchor data initial times timeZero dense limitLaw observedWeak
  let measure : ProbabilityMeasure (ActualStationaryElectricalSpace rule p positive belowOne fixedPoint natural.growth (natural.amplitude • natural.field) (zero_lt_one.trans natural.aboveOne) ⟨marks, typical.1.1⟩) := ⟨boundary.map realization, massProbability⟩
  letI : (measure : Measure (ActualStationaryElectricalSpace rule p positive belowOne fixedPoint natural.growth (natural.amplitude • natural.field)
      (zero_lt_one.trans natural.aboveOne) ⟨marks, typical.1.1⟩)).IsOpenPosMeasure := massOpenPositive
  obtain ⟨bound, boundPositive, bounded⟩ := density chemicalScale chemicalScalePositive
  intro countingSpeed ratios ratiosPositive ratio ratioPositive ratioConvergence
  apply actual_weighted_rescaled_global_weak_completion20261011 rule p positive belowOne fixedPoint natural.growth (natural.amplitude • natural.field)
    (zero_lt_one.trans natural.aboveOne) ⟨marks, typical⟩ chemicalScale chemicalScalePositive measure anchor
    (Nat.zero_lt_of_lt classicalRule.edges_gt_one) natural.aboveOne
    (degrees typical.1.1 boundary probability atoms realization projection chemicalScale chemicalScalePositive)
    stationary fields eta ((rule.edges + 1 : ℝ) / (1 - eta)) start etaPositive.le etaBelowOne
    (div_nonneg (by positivity) (sub_pos.mpr etaBelowOne).le) radiusBounds initial bound boundPositive.le
    (fun depth vertex => (bounded depth vertex).1.2) ?_ countingSpeed ratios ratiosPositive ratio ratioPositive ratioConvergence times dense limitLaw observedWeak
  exact centered typical compactness boundary probability atoms realization projection massProbability massOpenPositive
    chemicalScale chemicalScalePositive initial

end
end IGSIII34.Diffusion




