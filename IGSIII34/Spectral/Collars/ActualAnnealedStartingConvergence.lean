import IGSIII34.Spectral.Collars.ActualFiniteAnnealedCanonicalPath
import IGSIII34.ResistanceLimit.ActualStationaryCompletion
import IGSIII34.ResistanceLimit.ActualHarmonic
import IGSIII34.Percolation.Continuation.NaturalResistanceCompletion

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000
namespace IGSIII34.Spectral
noncomputable section
open Universality Universality.FiniteNetwork IGSIII.Geometry IGSIII.Chemical.Substitution
open IGSIII34.ResistanceLimit IGSIII34.Percolation IGSIII34.Diffusion MeasureTheory Filter
open scoped _root_.Topology

def actualAnnealedSelectedVertex (rule : Rule)
    (marks : (List (Fin rule.edges) × Bool) → Configuration rule.edges)
    (depth : ℕ) (initial : Fin (rule.generation depth).vertices) :
    RetainedSkeletonVertex (rule.generation depth).network (stationaryConfiguration rule marks depth) := by
  classical
  if retained : ((rule.generation depth).network.openGraph (stationaryConfiguration rule marks depth)).Reachable
      (rule.generation depth).network.source initial then
    exact ⟨initial, retained⟩
  else
    exact ⟨(rule.generation depth).network.source, SimpleGraph.Reachable.refl _⟩

/-- The legitimate starting-point condition is expressed in the original
actual completed carrier, whose topology is identified with the same
chemical carrier by the master homeomorphism. It assumes no path-law limit. -/
def ActualAnnealedStartingConvergence
    (rule : Rule) (p : ℝ) (positive : 0 < p) (belowOne : p < 1)
    (fixedPoint : rule.network.reliability p = p)
    (natural : NaturalResistanceCompletion rule p positive belowOne fixedPoint)
    (initial : ∀ depth, ((List (Fin rule.edges) × Bool) → Configuration rule.edges) →
      Fin (rule.generation depth).vertices) : Prop :=
  ∀ᵐ marks ∂independentInnovationLaw rule p positive belowOne fixedPoint,
    ∀ typical : StationaryHarmonicTypical rule p positive belowOne fixedPoint
        natural.growth (natural.amplitude • natural.field) marks,
    ∃ point : ActualStationaryElectricalSpace rule p positive belowOne fixedPoint natural.growth
        (natural.amplitude • natural.field) (zero_lt_one.trans natural.aboveOne) ⟨marks, typical.1.1⟩,
      Tendsto (fun depth => actualStationaryElectricalVertex rule p positive belowOne fixedPoint natural.growth
        (natural.amplitude • natural.field) (zero_lt_one.trans natural.aboveOne) ⟨marks, typical.1.1⟩ depth
        (actualAnnealedSelectedVertex rule marks depth (initial depth marks))) atTop (𝓝 point)

theorem actualAnnealedSelectedVertex_initial_probability_tendsto
    (rule : Rule) (p : ℝ) (positive : 0 < p) (belowOne : p < 1)
    (fixedPoint : rule.network.reliability p = p)
    (natural : NaturalResistanceCompletion rule p positive belowOne fixedPoint)
    (marks : (List (Fin rule.edges) × Bool) → Configuration rule.edges)
    (typical : StationaryHarmonicTypical rule p positive belowOne fixedPoint
      natural.growth (natural.amplitude • natural.field) marks)
    (initial : ∀ depth, Fin (rule.generation depth).vertices)
    (scale : ℝ) (scalePositive : 0 < scale)
    (point : ActualStationaryElectricalSpace rule p positive belowOne fixedPoint natural.growth
      (natural.amplitude • natural.field) (zero_lt_one.trans natural.aboveOne) ⟨marks, typical.1.1⟩)
    (convergence : Tendsto (fun depth => actualStationaryElectricalVertex rule p positive belowOne fixedPoint natural.growth
      (natural.amplitude • natural.field) (zero_lt_one.trans natural.aboveOne) ⟨marks, typical.1.1⟩ depth
      (actualAnnealedSelectedVertex rule marks depth (initial depth))) atTop (𝓝 point)) :
    letI : MeasurableSpace (ActualStationaryElectricalSpace rule p positive belowOne fixedPoint natural.growth
      (natural.amplitude • natural.field) (zero_lt_one.trans natural.aboveOne) ⟨marks, typical.1.1⟩) := borel _
    letI : BorelSpace (ActualStationaryElectricalSpace rule p positive belowOne fixedPoint natural.growth
      (natural.amplitude • natural.field) (zero_lt_one.trans natural.aboveOne) ⟨marks, typical.1.1⟩) := ⟨rfl⟩
    Tendsto (fun depth => (diracProba (X := ActualFiniteCluster rule (stationaryConfiguration rule marks) scale scalePositive depth)
        (actualAnnealedSelectedVertex rule marks depth (initial depth))).map
      (measurable_of_finite (fun vertex : ActualFiniteCluster rule (stationaryConfiguration rule marks) scale scalePositive depth =>
        actualStationaryElectricalVertex rule p positive belowOne fixedPoint natural.growth
          (natural.amplitude • natural.field) (zero_lt_one.trans natural.aboveOne) ⟨marks, typical.1.1⟩ depth vertex)).aemeasurable)
      atTop (𝓝 (diracProba point)) := by
  letI : MeasurableSpace (ActualStationaryElectricalSpace rule p positive belowOne fixedPoint natural.growth
      (natural.amplitude • natural.field) (zero_lt_one.trans natural.aboveOne) ⟨marks, typical.1.1⟩) := borel _
  letI : BorelSpace (ActualStationaryElectricalSpace rule p positive belowOne fixedPoint natural.growth
      (natural.amplitude • natural.field) (zero_lt_one.trans natural.aboveOne) ⟨marks, typical.1.1⟩) := ⟨rfl⟩
  have weak := continuous_diracProba.continuousAt.tendsto.comp convergence
  convert weak using 1
  funext depth
  apply ProbabilityMeasure.toMeasure_injective
  simp only [ProbabilityMeasure.toMeasure_map, diracProba]
  exact Measure.map_dirac' (measurable_of_finite _) _

end
end IGSIII34.Spectral
