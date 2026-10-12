import IGSIII34.Diffusion.ObservedWalkSpectralMomentsCompletion
import IGSIII34.Diffusion.SpectralCorrectorEulerErrorCompletion
import IGSIII34.Diffusion.ActualPaperClockGrowthCompletion
import IGSIII34.Diffusion.ActualResolventUniformCompletion
import IGSIII34.Spectral.ActualEigenfunctionCorrectorCompletion
import IGSIII34.Diffusion.ActualResolventWholePointwiseCompletion
import IGSIII34.Diffusion.ActualPrescribedLimitEnergyCompletion
import IGSIII34.Diffusion.UniqueSkeletonLimitCompletion
import IGSIII34.Diffusion.ActualHarmonicObjectiveUniquenessCompletion
import IGSIII34.Diffusion.ActualConstructedRecoveryCompletion
import IGSIII34.Diffusion.ProbabilityWeakMetricCompletion
import IGSIII34.Diffusion.ElectricalDegreeProjectionCompletion

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

local instance actualWalkIdentificationCarrierMeasurableCompletion : MeasurableSpace
    (ActualStationaryElectricalSpace rule p positive belowOne fixedPoint growth value growthPositive ⟨marks.val, marks.property.1.1⟩) := borel _
local instance actualWalkIdentificationCarrierBorelCompletion : BorelSpace
    (ActualStationaryElectricalSpace rule p positive belowOne fixedPoint growth value growthPositive ⟨marks.val, marks.property.1.1⟩) := ⟨rfl⟩

variable [CompactSpace (ActualStationaryElectricalSpace rule p positive belowOne fixedPoint growth value growthPositive ⟨marks.val, marks.property.1.1⟩)]
  (chemicalScale : ℝ) (chemicalScalePositive : 0 < chemicalScale)
  (measure : ProbabilityMeasure (ActualStationaryElectricalSpace rule p positive belowOne fixedPoint growth value growthPositive ⟨marks.val, marks.property.1.1⟩))

variable (anchor : ActualStationaryEnergySkeleton rule p positive belowOne fixedPoint growth value growthPositive
  (harmonicTypicalEnergyMarks rule p positive belowOne fixedPoint growth value marks))
  [(measure : Measure (ActualStationaryElectricalSpace rule p positive belowOne fixedPoint growth value growthPositive ⟨marks.val, marks.property.1.1⟩)).IsOpenPosMeasure]

local instance ActualWalkIdentificationCompletionCompact : CompactSpace
    (UniformSpace.Completion (ActualStationaryEnergySkeleton rule p positive belowOne fixedPoint growth value growthPositive
      (harmonicTypicalEnergyMarks rule p positive belowOne fixedPoint growth value marks))) := by
  change CompactSpace (ActualStationaryElectricalSpace rule p positive belowOne fixedPoint growth value growthPositive ⟨marks.val, marks.property.1.1⟩)
  infer_instance
local instance ActualWalkIdentificationCompletionMeasurable : MeasurableSpace
    (UniformSpace.Completion (ActualStationaryEnergySkeleton rule p positive belowOne fixedPoint growth value growthPositive
      (harmonicTypicalEnergyMarks rule p positive belowOne fixedPoint growth value marks))) := borel _
local instance ActualWalkIdentificationCompletionBorel : BorelSpace
    (UniformSpace.Completion (ActualStationaryEnergySkeleton rule p positive belowOne fixedPoint growth value growthPositive
      (harmonicTypicalEnergyMarks rule p positive belowOne fixedPoint growth value marks))) := ⟨rfl⟩

open IGSIII34.Spectral ProbabilityTheory
local instance actualWalkIdentificationNormCompletion : NormedAddCommGroup
    (actualAnchoredEnergyDomainCompletion rule p positive belowOne fixedPoint growth value growthPositive
      (harmonicTypicalEnergyMarks rule p positive belowOne fixedPoint growth value marks) anchor) :=
  actualAnchoredNormedAddCommGroup rule p positive belowOne fixedPoint growth value growthPositive
    (harmonicTypicalEnergyMarks rule p positive belowOne fixedPoint growth value marks) anchor
local instance actualWalkIdentificationUniformCompletion : UniformSpace
    (actualAnchoredEnergyDomainCompletion rule p positive belowOne fixedPoint growth value growthPositive
      (harmonicTypicalEnergyMarks rule p positive belowOne fixedPoint growth value marks) anchor) :=
  (actualWalkIdentificationNormCompletion rule p positive belowOne fixedPoint growth value growthPositive marks anchor).toMetricSpace.toUniformSpace
local instance actualWalkIdentificationTopologyCompletion : TopologicalSpace
    (actualAnchoredEnergyDomainCompletion rule p positive belowOne fixedPoint growth value growthPositive
      (harmonicTypicalEnergyMarks rule p positive belowOne fixedPoint growth value marks) anchor) :=
  (actualWalkIdentificationNormCompletion rule p positive belowOne fixedPoint growth value growthPositive marks anchor).toMetricSpace.toUniformSpace.toTopologicalSpace
local instance actualWalkIdentificationInnerCompletion : InnerProductSpace ℝ
    (actualAnchoredEnergyDomainCompletion rule p positive belowOne fixedPoint growth value growthPositive
      (harmonicTypicalEnergyMarks rule p positive belowOne fixedPoint growth value marks) anchor) :=
  actualAnchoredInnerProductSpace rule p positive belowOne fixedPoint growth value growthPositive
    (harmonicTypicalEnergyMarks rule p positive belowOne fixedPoint growth value marks) anchor

local instance actualWalkIdentificationCompleteCompletion : CompleteSpace
    (actualAnchoredEnergyDomainCompletion rule p positive belowOne fixedPoint growth value growthPositive
      (harmonicTypicalEnergyMarks rule p positive belowOne fixedPoint growth value marks) anchor) :=
  actual_anchored_completeSpace rule p positive belowOne fixedPoint growth value growthPositive
    (harmonicTypicalEnergyMarks rule p positive belowOne fixedPoint growth value marks) anchor

/-- Every weak observation limit of the actual manuscript-clock walk has
the genuine spectral conditional moments. Corrector convergence and its
generator equation are proved here from the original networks. -/
theorem actual_walk_limit_paired_spectral_moments_completion
    (degreeLimit : Tendsto (fun depth => levyProkhorovEDist
      (actualElectricalDegreeMeasureCompletion rule p positive belowOne fixedPoint growth value growthPositive
        ⟨marks.val, marks.property.1.1⟩ chemicalScale chemicalScalePositive depth) (measure : Measure (ActualStationaryElectricalSpace rule p positive belowOne fixedPoint growth value growthPositive ⟨marks.val, marks.property.1.1⟩))) atTop (𝓝 0))
    (stationary : ∀ address, electricalCell rule.network (marks.val (address, true))
      (fun edge => electricalField rule p positive belowOne fixedPoint value (address ++ [edge]) marks.val) =
        growth * electricalField rule p positive belowOne fixedPoint value address marks.val)
    (fieldLimit : ∀ address, Tendsto (fun depth => growth⁻¹ ^ depth * electricalIteration rule marks.val depth address) atTop
      (𝓝 (electricalField rule p positive belowOne fixedPoint value address marks.val)))
    (eta coefficient : ℝ) (start : ℕ) (etaNonnegative : 0 ≤ eta) (etaBelowOne : eta < 1)
    (coefficientNonnegative : 0 ≤ coefficient)
    (radiusBound : ∀ address opened depth, start ≤ address.length →
      markedElectricalRadius rule marks.val depth address opened / growth ^ (depth + 1 + address.length) ≤ coefficient * eta ^ address.length)
    (growthGreaterThanOne : 1 < growth)
    (data : ActualSpectralDataCompletion rule p positive belowOne fixedPoint growth value growthPositive
      (harmonicTypicalEnergyMarks rule p positive belowOne fixedPoint growth value marks) anchor
      (measure : Measure (ActualStationaryElectricalSpace rule p positive belowOne fixedPoint growth value growthPositive ⟨marks.val, marks.property.1.1⟩)))
    (index : data.index)
    (initial : ∀ depth, ProbabilityMeasure (ActualFiniteCluster rule (stationaryConfiguration rule marks.val) chemicalScale chemicalScalePositive depth))
    (times : ℕ → ℝ≥0) (selected : ℕ → ℕ) (selectedAtTop : Tendsto selected atTop atTop)
    (limitLaw : ProbabilityMeasure (ℕ → ActualStationaryElectricalSpace rule p positive belowOne fixedPoint growth value growthPositive ⟨marks.val, marks.property.1.1⟩))
    (weak : Tendsto (fun depth => discreteRescaledObservationLawCompletion
      (Vertex := ActualFiniteCluster rule (stationaryConfiguration rule marks.val) chemicalScale chemicalScalePositive (selected depth))
      (clusterRetainedEndpoint (rule.generation (selected depth)).network (stationaryConfiguration rule marks.val (selected depth)))
      (cluster_degree_positive _ _ (markedGenerationConfiguration_crosses rule marks.val marks.property.1.1.2.1 (selected depth) [] true))
      (initial (selected depth))
      (actualPaperDiscreteClockCompletion rule p positive belowOne fixedPoint growth value ⟨marks.val, marks.property.1.1⟩ (selected depth)) times
      (fun vertex : ActualFiniteCluster rule (stationaryConfiguration rule marks.val) chemicalScale chemicalScalePositive (selected depth) =>
        actualStationaryElectricalVertex rule p positive belowOne fixedPoint growth value growthPositive ⟨marks.val, marks.property.1.1⟩ (selected depth) vertex)) atTop (𝓝 limitLaw))
    {count : ℕ} (pastCoordinates : Fin count → ℕ) (startCoordinate futureCoordinate : ℕ)
    (before : ∀ coordinate, times (pastCoordinates coordinate) ≤ times startCoordinate)
    (ordered : times startCoordinate ≤ times futureCoordinate)
    (past : C((Fin count → ActualStationaryElectricalSpace rule p positive belowOne fixedPoint growth value growthPositive ⟨marks.val, marks.property.1.1⟩), ℝ)) :
    (∫ path : ℕ → ActualStationaryElectricalSpace rule p positive belowOne fixedPoint growth value growthPositive ⟨marks.val, marks.property.1.1⟩, past (fun coordinate => path (pastCoordinates coordinate)) *
      actualSpectralEigenfunctionsCompletion rule p positive belowOne fixedPoint growth value growthPositive
        (harmonicTypicalEnergyMarks rule p positive belowOne fixedPoint growth value marks) anchor (measure : Measure (ActualStationaryElectricalSpace rule p positive belowOne fixedPoint growth value growthPositive ⟨marks.val, marks.property.1.1⟩)) data index
        (path futureCoordinate) ∂limitLaw) =
      Real.exp (-((data.resolventEigenvalues index)⁻¹ - 1) * ((times futureCoordinate : ℝ) - times startCoordinate)) *
        (∫ path : ℕ → ActualStationaryElectricalSpace rule p positive belowOne fixedPoint growth value growthPositive ⟨marks.val, marks.property.1.1⟩, past (fun coordinate => path (pastCoordinates coordinate)) *
          actualSpectralEigenfunctionsCompletion rule p positive belowOne fixedPoint growth value growthPositive
            (harmonicTypicalEnergyMarks rule p positive belowOne fixedPoint growth value marks) anchor (measure : Measure (ActualStationaryElectricalSpace rule p positive belowOne fixedPoint growth value growthPositive ⟨marks.val, marks.property.1.1⟩)) data index
            (path startCoordinate) ∂limitLaw) := by
  let vertices := fun depth => ActualFiniteCluster rule (stationaryConfiguration rule marks.val) chemicalScale chemicalScalePositive depth
  let endpoint : ∀ depth, ClusterEdge (rule.generation depth).network (stationaryConfiguration rule marks.val depth) → vertices depth × vertices depth := fun depth => clusterRetainedEndpoint (rule.generation depth).network (stationaryConfiguration rule marks.val depth)
  let positiveDegree : ∀ depth vertex, 0 < degree (endpoint depth) vertex := fun depth => cluster_degree_positive (rule.generation depth).network (stationaryConfiguration rule marks.val depth)
    (markedGenerationConfiguration_crosses rule marks.val marks.property.1.1.2.1 depth [] true)
  let placement := fun depth (vertex : vertices depth) => actualStationaryElectricalVertex rule p positive belowOne fixedPoint growth value growthPositive
    ⟨marks.val, marks.property.1.1⟩ depth vertex
  let clocks := actualPaperDiscreteClockCompletion rule p positive belowOne fixedPoint growth value ⟨marks.val, marks.property.1.1⟩
  let eigenfunction := actualSpectralEigenfunctionsCompletion rule p positive belowOne fixedPoint growth value growthPositive
    (harmonicTypicalEnergyMarks rule p positive belowOne fixedPoint growth value marks) anchor (measure : Measure (ActualStationaryElectricalSpace rule p positive belowOne fixedPoint growth value growthPositive ⟨marks.val, marks.property.1.1⟩)) data index
  let eigenvalue := (data.resolventEigenvalues index)⁻¹ - 1
  let correctors := fun depth => actualPaperClockGraphResolventCompletion rule (stationaryConfiguration rule marks.val)
    (fun depth => markedGenerationConfiguration_crosses rule marks.val marks.property.1.1.2.1 depth [] true)
    chemicalScale chemicalScalePositive depth growth growthPositive 1 (by norm_num)
    (fun vertex : vertices depth => (1 + eigenvalue) * eigenfunction (placement depth vertex))
  have uniform : ∀ tolerance : ℝ, 0 < tolerance → ∀ᶠ depth in atTop,
      ∀ vertex : vertices depth, |correctors depth vertex - eigenfunction (placement depth vertex)| < tolerance := by
    intro tolerance positiveTolerance
    have actual := actualOriginalResolvent_uniform_completion rule p positive belowOne fixedPoint growth value growthPositive
      marks chemicalScale chemicalScalePositive measure anchor degreeLimit stationary fieldLimit eta coefficient start etaNonnegative etaBelowOne
      coefficientNonnegative radiusBound 1 le_rfl (by norm_num) ((1 + eigenvalue) • eigenfunction) tolerance positiveTolerance
    have identity := actual_eigenfunction_resolvent_corrector_completion rule p positive belowOne fixedPoint growth value growthPositive
      (harmonicTypicalEnergyMarks rule p positive belowOne fixedPoint growth value marks) anchor (measure : Measure (ActualStationaryElectricalSpace rule p positive belowOne fixedPoint growth value growthPositive ⟨marks.val, marks.property.1.1⟩)) data index
    filter_upwards [actual] with depth close
    intro vertex
    have bound := close vertex
    rw [identity] at bound
    simp only [actualOriginalPaperClockResolventPotentialCompletion,
      retainedPotentialExtension_retained_completion, ContinuousMap.smul_apply, smul_eq_mul] at bound
    convert bound using 1 <;> congr 1
  have errorsUniform := uniform_corrector_euler_error_completion vertices placement eigenfunction eigenvalue correctors uniform
  have clockPositive := actualPaperDiscreteClock_positive_completion rule p positive belowOne fixedPoint growth value growthPositive
    ⟨marks.val, marks.property.1.1⟩
  have clockDiverges := actualPaperDiscreteClock_diverges_completion rule p positive belowOne fixedPoint growth value growthPositive
    ⟨marks.val, marks.property.1.1⟩ growthGreaterThanOne
  have generator (depth : ℕ) (vertex : vertices depth) : clocks depth * rateOneGenerator (endpoint depth) (correctors depth) vertex =
      -eigenvalue * correctors depth vertex + (1 + eigenvalue) * (correctors depth vertex - eigenfunction (placement depth vertex)) := by
    exact finite_resolvent_corrector_euler_equation_completion (endpoint depth) (positiveDegree depth)
      (clocks depth) (clockPositive depth).le eigenvalue (fun vertex => eigenfunction (placement depth vertex)) vertex
  exact discrete_walk_limit_paired_spectral_moments_completion
    (fun depth => vertices (selected depth))
    (fun depth => ClusterEdge (rule.generation (selected depth)).network (stationaryConfiguration rule marks.val (selected depth)))
    (fun depth => endpoint (selected depth)) (fun depth => positiveDegree (selected depth))
    (fun depth => initial (selected depth)) (fun depth => placement (selected depth))
    (fun depth => clocks (selected depth)) (fun depth => clockPositive (selected depth)) (clockDiverges.comp selectedAtTop)
    times limitLaw weak eigenfunction eigenvalue (data.generatorNonnegative index)
    (fun depth => correctors (selected depth))
    (fun depth vertex => (1 + eigenvalue) * (correctors (selected depth) vertex - eigenfunction (placement (selected depth) vertex)))
    (fun depth => generator (selected depth))
    (fun tolerance positiveTolerance => selectedAtTop.eventually (uniform tolerance positiveTolerance))
    (fun tolerance positiveTolerance => selectedAtTop.eventually (errorsUniform tolerance positiveTolerance))
    pastCoordinates startCoordinate futureCoordinate before ordered past

end
end IGSIII34.Diffusion









