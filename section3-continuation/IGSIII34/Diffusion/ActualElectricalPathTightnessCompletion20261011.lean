import IGSIII34.Diffusion.ActualCutoffResolventApproximationCompletion20261011
import IGSIII34.Diffusion.ActualWalkSmallJumpsCompletion20261011
import IGSIII34.Diffusion.ResolventCutoffTightnessCompletion20261011
import IGSIII34.Diffusion.CountableProcessJointMeasurabilityCompletion20261011
import IGSIII34.Diffusion.CompactPlateauCoverCompletion20261011
import IGSIII34.Diffusion.ActualScaledContinuousResolventCompletion20261011
import IGSIII34.Diffusion.ActualPaperClockGrowthCompletion20261011
import IGSIII34.Diffusion.ActualWholeContinuousResolventCompletion20261011
import IGSIII34.Forms.ActualRegularityCompletion20261011
import IGSIII34.Diffusion.ActualResolventWholePointwiseCompletion20261011
import IGSIII34.Diffusion.ActualPrescribedLimitEnergyCompletion20261011
import IGSIII34.Diffusion.UniqueSkeletonLimitCompletion20261011
import IGSIII34.Diffusion.ActualHarmonicObjectiveUniquenessCompletion20261011
import IGSIII34.Diffusion.ActualConstructedRecoveryCompletion20261011
import IGSIII34.Diffusion.ProbabilityWeakMetricCompletion20261011
import IGSIII34.Diffusion.ElectricalDegreeProjectionCompletion20261011

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option backward.isDefEq.respectTransparency false
namespace IGSIII34.Diffusion
noncomputable section
open Universality Universality.FiniteNetwork IGSIII34.ResistanceLimit IGSIII34.Percolation
open IGSIII.Chemical.Substitution IGSIII.Geometry IGSIII34.Forms MeasureTheory Filter
open scoped _root_.Topology BigOperators NNReal

variable (rule : Rule) (p : ℝ) (positive : 0 < p) (belowOne : p < 1)
  (fixedPoint : rule.network.reliability p = p) (growth : ℝ)
  (value : Lp ℝ 2 (independentInnovationLaw rule p positive belowOne fixedPoint))
  (growthPositive : 0 < growth)
  (marks : {marks // StationaryHarmonicTypical rule p positive belowOne fixedPoint growth value marks})

local instance pathTightnessCarrierMeasurableCompletion20261011 : MeasurableSpace
    (ActualStationaryElectricalSpace rule p positive belowOne fixedPoint growth value growthPositive ⟨marks.val, marks.property.1.1⟩) := borel _
local instance pathTightnessCarrierBorelCompletion20261011 : BorelSpace
    (ActualStationaryElectricalSpace rule p positive belowOne fixedPoint growth value growthPositive ⟨marks.val, marks.property.1.1⟩) := ⟨rfl⟩

variable [CompactSpace (ActualStationaryElectricalSpace rule p positive belowOne fixedPoint growth value growthPositive ⟨marks.val, marks.property.1.1⟩)]
  (chemicalScale : ℝ) (chemicalScalePositive : 0 < chemicalScale)
  (measure : ProbabilityMeasure (ActualStationaryElectricalSpace rule p positive belowOne fixedPoint growth value growthPositive ⟨marks.val, marks.property.1.1⟩))

variable (anchor : ActualStationaryEnergySkeleton rule p positive belowOne fixedPoint growth value growthPositive
  (harmonicTypicalEnergyMarks rule p positive belowOne fixedPoint growth value marks))
  [(measure : Measure (ActualStationaryElectricalSpace rule p positive belowOne fixedPoint growth value growthPositive ⟨marks.val, marks.property.1.1⟩)).IsOpenPosMeasure]

local instance ActualPathTightnessCompletion20261011Compact : CompactSpace
    (UniformSpace.Completion (ActualStationaryEnergySkeleton rule p positive belowOne fixedPoint growth value growthPositive
      (harmonicTypicalEnergyMarks rule p positive belowOne fixedPoint growth value marks))) := by
  change CompactSpace (ActualStationaryElectricalSpace rule p positive belowOne fixedPoint growth value growthPositive ⟨marks.val, marks.property.1.1⟩)
  infer_instance
local instance ActualPathTightnessCompletion20261011Measurable : MeasurableSpace
    (UniformSpace.Completion (ActualStationaryEnergySkeleton rule p positive belowOne fixedPoint growth value growthPositive
      (harmonicTypicalEnergyMarks rule p positive belowOne fixedPoint growth value marks))) := borel _
local instance ActualPathTightnessCompletion20261011Borel : BorelSpace
    (UniformSpace.Completion (ActualStationaryEnergySkeleton rule p positive belowOne fixedPoint growth value growthPositive
      (harmonicTypicalEnergyMarks rule p positive belowOne fixedPoint growth value marks))) := ⟨rfl⟩

open IGSIII34.Spectral
local instance actualPathTightnessNormCompletion20261011 : NormedAddCommGroup
    (actualAnchoredEnergyDomainCompletion20261011 rule p positive belowOne fixedPoint growth value growthPositive
      (harmonicTypicalEnergyMarks rule p positive belowOne fixedPoint growth value marks) anchor) :=
  actualAnchoredNormedAddCommGroup rule p positive belowOne fixedPoint growth value growthPositive
    (harmonicTypicalEnergyMarks rule p positive belowOne fixedPoint growth value marks) anchor
local instance actualPathTightnessCutoffApproximationCompletion20261011 : UniformSpace
    (actualAnchoredEnergyDomainCompletion20261011 rule p positive belowOne fixedPoint growth value growthPositive
      (harmonicTypicalEnergyMarks rule p positive belowOne fixedPoint growth value marks) anchor) :=
  (actualPathTightnessNormCompletion20261011 rule p positive belowOne fixedPoint growth value growthPositive marks anchor).toMetricSpace.toUniformSpace
local instance actualPathTightnessTopologyCompletion20261011 : TopologicalSpace
    (actualAnchoredEnergyDomainCompletion20261011 rule p positive belowOne fixedPoint growth value growthPositive
      (harmonicTypicalEnergyMarks rule p positive belowOne fixedPoint growth value marks) anchor) :=
  (actualPathTightnessNormCompletion20261011 rule p positive belowOne fixedPoint growth value growthPositive marks anchor).toMetricSpace.toUniformSpace.toTopologicalSpace
local instance actualPathTightnessInnerCompletion20261011 : InnerProductSpace ℝ
    (actualAnchoredEnergyDomainCompletion20261011 rule p positive belowOne fixedPoint growth value growthPositive
      (harmonicTypicalEnergyMarks rule p positive belowOne fixedPoint growth value marks) anchor) :=
  actualAnchoredInnerProductSpace rule p positive belowOne fixedPoint growth value growthPositive
    (harmonicTypicalEnergyMarks rule p positive belowOne fixedPoint growth value marks) anchor

local instance actualPathTightnessCompleteCompletion20261011 : CompleteSpace
    (actualAnchoredEnergyDomainCompletion20261011 rule p positive belowOne fixedPoint growth value growthPositive
      (harmonicTypicalEnergyMarks rule p positive belowOne fixedPoint growth value marks) anchor) :=
  actual_anchored_completeSpace rule p positive belowOne fixedPoint growth value growthPositive
    (harmonicTypicalEnergyMarks rule p positive belowOne fixedPoint growth value marks) anchor

include anchor in
theorem actual_discrete_countable_modulus_probability_completion20261011
    (edgePositive : 0 < rule.edges) (growthGreaterThanOne : 1 < growth)
    (degreeLimit : Tendsto (fun depth => levyProkhorovEDist
      (actualElectricalDegreeMeasureCompletion20261011 rule p positive belowOne fixedPoint growth value growthPositive
        ⟨marks.val, marks.property.1.1⟩ chemicalScale chemicalScalePositive depth) (measure : Measure _)) atTop (𝓝 0))
    (stationary : ∀ address, electricalCell rule.network (marks.val (address, true))
      (fun edge => electricalField rule p positive belowOne fixedPoint value (address ++ [edge]) marks.val) =
        growth * electricalField rule p positive belowOne fixedPoint value address marks.val)
    (fieldLimit : ∀ address, Tendsto (fun depth => growth⁻¹ ^ depth * electricalIteration rule marks.val depth address) atTop
      (𝓝 (electricalField rule p positive belowOne fixedPoint value address marks.val)))
    (eta coefficient : ℝ) (start : ℕ) (etaNonnegative : 0 ≤ eta) (etaBelowOne : eta < 1)
    (coefficientNonnegative : 0 ≤ coefficient)
    (radiusBound : ∀ address opened depth, start ≤ address.length →
      markedElectricalRadius rule marks.val depth address opened / growth ^ (depth + 1 + address.length) ≤ coefficient * eta ^ address.length)

    (times : ℕ → ℝ≥0)
    (initial : ∀ depth, ProbabilityMeasure (ActualFiniteCluster rule (stationaryConfiguration rule marks.val) chemicalScale chemicalScalePositive depth))
    (horizon : ℕ) (tolerance probability : ℝ) (tolerancePositive : 0 < tolerance) (probabilityPositive : 0 < probability) :
    ∃ duration : ℝ, 0 < duration ∧ ∀ᶠ depth in atTop,
      (actualPaperDiscreteElectricalObservationLawCompletion20261011 rule p positive belowOne fixedPoint growth value
        growthPositive ⟨marks.val, marks.property.1.1⟩ chemicalScale chemicalScalePositive times initial depth : Measure (ℕ → ActualStationaryElectricalSpace rule p positive belowOne fixedPoint growth value growthPositive ⟨marks.val, marks.property.1.1⟩)).real
        (countableTimeBadModulusCompletion20261011 times horizon duration tolerance) ≤ probability := by
  let radius := tolerance / 4
  have radiusPositive : 0 < radius := by dsimp only [radius]; positivity
  obtain ⟨centers, finite, cover⟩ := exists_compact_plateau_cover_completion20261011
    (Space := ActualStationaryElectricalSpace rule p positive belowOne fixedPoint growth value growthPositive ⟨marks.val, marks.property.1.1⟩)
    radius radiusPositive
  letI : Fintype centers := finite.fintype
  letI : Nonempty centers := by
    obtain ⟨center, _⟩ := cover
      (anchor : UniformSpace.Completion (ActualStationaryEnergySkeleton rule p positive belowOne fixedPoint growth value growthPositive
        (harmonicTypicalEnergyMarks rule p positive belowOne fixedPoint growth value marks)))
    exact ⟨center⟩
  letI : ∀ depth, Nonempty (ActualFiniteCluster rule (stationaryConfiguration rule marks.val) chemicalScale chemicalScalePositive depth) :=
    fun depth => ⟨⟨(rule.generation depth).network.source, SimpleGraph.Reachable.refl _⟩⟩
  have clocksPositive := actualPaperDiscreteClock_positive_completion20261011 rule p positive belowOne fixedPoint growth value growthPositive
    ⟨marks.val, marks.property.1.1⟩
  have clocksDiverge := actualPaperDiscreteClock_diverges_completion20261011 rule p positive belowOne fixedPoint growth value growthPositive
    ⟨marks.val, marks.property.1.1⟩ growthGreaterThanOne
  have jumps := actualElectrical_walk_eventually_small_jumps_completion20261011 rule edgePositive p positive belowOne fixedPoint growth value
    growthPositive ⟨marks.val, marks.property.1.1⟩ fieldLimit eta coefficient start etaNonnegative etaBelowOne radiusBound
    chemicalScale chemicalScalePositive initial radius radiusPositive
  have approximations : ∀ error : ℝ, 0 < error → ∃ parameter : ℝ, ∃ parameterPositive : 0 < parameter,
      1 ≤ parameter ∧ ∀ᶠ depth in atTop, ∀ (label : centers) vertex,
        |finiteGraphResolvent
          (Vertex := ActualFiniteCluster rule (stationaryConfiguration rule marks.val) chemicalScale chemicalScalePositive depth)
          (clusterRetainedEndpoint (rule.generation depth).network (stationaryConfiguration rule marks.val depth))
          (cluster_degree_positive _ _ (markedGenerationConfiguration_crosses rule marks.val marks.property.1.1.2.1 depth [] true))
          parameter (actualPaperDiscreteClockCompletion20261011 rule p positive belowOne fixedPoint growth value ⟨marks.val, marks.property.1.1⟩ depth)
          parameterPositive (clocksPositive depth).le
          (fun point => parameter * compactPlateauCompletion20261011 (Subtype.val label) radius
            (actualStationaryElectricalVertex rule p positive belowOne fixedPoint growth value growthPositive ⟨marks.val, marks.property.1.1⟩ depth point)) vertex -
          compactPlateauCompletion20261011 (Subtype.val label) radius
            (actualStationaryElectricalVertex rule p positive belowOne fixedPoint growth value growthPositive ⟨marks.val, marks.property.1.1⟩ depth vertex)| ≤ error := by
    intro error positiveError
    simpa only [actualPaperClockGraphResolventCompletion20261011, actualPaperDiscreteClockCompletion20261011] using
      actual_plateau_finite_resolvent_approximation_completion20261011 rule p positive belowOne fixedPoint growth value growthPositive marks
        chemicalScale chemicalScalePositive measure anchor degreeLimit stationary fieldLimit eta coefficient start etaNonnegative etaBelowOne
        coefficientNonnegative radiusBound centers Subtype.val radius error positiveError
  have bounds := finite_resolvent_cutoff_tightness_completion20261011
    (fun depth => ActualFiniteCluster rule (stationaryConfiguration rule marks.val) chemicalScale chemicalScalePositive depth)
    (fun depth => ClusterEdge (rule.generation depth).network (stationaryConfiguration rule marks.val depth))
    (fun depth => clusterRetainedEndpoint (rule.generation depth).network (stationaryConfiguration rule marks.val depth))
    (fun depth => cluster_degree_positive _ _ (markedGenerationConfiguration_crosses rule marks.val marks.property.1.1.2.1 depth [] true))
    initial times (fun depth vertex => actualStationaryElectricalVertex rule p positive belowOne fixedPoint growth value growthPositive
      ⟨marks.val, marks.property.1.1⟩ depth vertex) (fun depth => measurable_of_finite _)
    _ clocksPositive clocksDiverge Subtype.val radius radiusPositive cover approximations jumps horizon probability probabilityPositive
  have identity (depth : ℕ) :
      (actualPaperDiscreteElectricalObservationLawCompletion20261011 rule p positive belowOne fixedPoint growth value growthPositive
        ⟨marks.val, marks.property.1.1⟩ chemicalScale chemicalScalePositive times initial depth :
        Measure (ℕ → ActualStationaryElectricalSpace rule p positive belowOne fixedPoint growth value growthPositive ⟨marks.val, marks.property.1.1⟩)) =
      (finiteDiscreteWalkLaw
        (Vertex := ActualFiniteCluster rule (stationaryConfiguration rule marks.val) chemicalScale chemicalScalePositive depth)
        (clusterRetainedEndpoint (rule.generation depth).network (stationaryConfiguration rule marks.val depth))
        (cluster_degree_positive _ _ (markedGenerationConfiguration_crosses rule marks.val marks.property.1.1.2.1 depth [] true)) (initial depth)).map
        (flooredCountableObservationCompletion20261011 times
          (fun vertex : ActualFiniteCluster rule (stationaryConfiguration rule marks.val) chemicalScale chemicalScalePositive depth =>
            actualStationaryElectricalVertex rule p positive belowOne fixedPoint growth value growthPositive ⟨marks.val, marks.property.1.1⟩ depth vertex)
          (actualPaperDiscreteClockCompletion20261011 rule p positive belowOne fixedPoint growth value ⟨marks.val, marks.property.1.1⟩ depth)) := rfl
  obtain ⟨duration, durationPositive, bounded⟩ := bounds
  refine ⟨duration, durationPositive, ?_⟩
  filter_upwards [bounded] with depth bound
  rw [identity depth]
  have toleranceIdentity : 4 * radius = tolerance := by dsimp only [radius]; ring
  rwa [toleranceIdentity] at bound

end
end IGSIII34.Diffusion



