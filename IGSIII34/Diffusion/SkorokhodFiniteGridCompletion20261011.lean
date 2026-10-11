import IGSIII34.Diffusion.SkorokhodJ1TopologyCompletion20261011
import Mathlib.Topology.MetricSpace.Pseudo.Pi
import Mathlib.MeasureTheory.Constructions.BorelSpace.Metric
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure

set_option autoImplicit false
set_option maxHeartbeats 1800000
namespace IGSIII34.Diffusion
noncomputable section
open MeasureTheory Filter Set
open scoped Topology ENNReal NNReal

variable {Space : Type*} [MetricSpace Space]

instance skorokhodJ1MeasurableCompletion20261011 :
    MeasurableSpace (SkorokhodIntervalPathCompletion20261011 Space) := borel _
instance skorokhodJ1BorelCompletion20261011 :
    BorelSpace (SkorokhodIntervalPathCompletion20261011 Space) := ⟨rfl⟩

def skorokhodFiniteReconstructionCompletion20261011 {count : ℕ}
    (selection : SkorokhodIntervalTimeCompletion20261011 → Fin count)
    (values : Fin count → Space) : SkorokhodIntervalPathCompletion20261011 Space :=
  ⟨fun time => values (selection time)⟩

theorem skorokhodFiniteReconstruction_lipschitz_completion20261011 {count : ℕ}
    (selection : SkorokhodIntervalTimeCompletion20261011 → Fin count) :
    LipschitzWith 1 (skorokhodFiniteReconstructionCompletion20261011 (Space := Space) selection) := by
  apply LipschitzWith.of_edist_le
  intro first second
  apply (skorokhodJ1EDist_le_uniform_completion20261011 _ _).trans
  apply iSup_le
  intro time
  exact edist_le_pi_edist first second (selection time)

theorem skorokhodFiniteReconstruction_measurable_completion20261011
    [MeasurableSpace Space] [BorelSpace Space] [SecondCountableTopology Space] {count : ℕ}
    (selection : SkorokhodIntervalTimeCompletion20261011 → Fin count) :
    Measurable (skorokhodFiniteReconstructionCompletion20261011 (Space := Space) selection) :=
  (skorokhodFiniteReconstruction_lipschitz_completion20261011 selection).continuous.measurable

theorem skorokhod_reconstructed_sample_measurable_completion20261011
    [MeasurableSpace Space] [BorelSpace Space] [SecondCountableTopology Space]
    {Outcome : Type*} [MeasurableSpace Outcome] {count : ℕ}
    (selection : SkorokhodIntervalTimeCompletion20261011 → Fin count)
    (sample : Outcome → Fin count → Space) (sampleMeasurable : Measurable sample) :
    Measurable (fun outcome => skorokhodFiniteReconstructionCompletion20261011 selection (sample outcome)) :=
  (skorokhodFiniteReconstruction_measurable_completion20261011 selection).comp sampleMeasurable

theorem skorokhod_reconstruction_weak_convergence_completion20261011
    [MeasurableSpace Space] [BorelSpace Space] [SecondCountableTopology Space] {count : ℕ}
    (selection : SkorokhodIntervalTimeCompletion20261011 → Fin count)
    (laws : ℕ → ProbabilityMeasure (Fin count → Space))
    (law : ProbabilityMeasure (Fin count → Space)) (convergence : Tendsto laws atTop (𝓝 law)) :
    Tendsto (fun index => (laws index).map (skorokhodFiniteReconstruction_measurable_completion20261011 selection).aemeasurable)
      atTop (𝓝 (law.map (skorokhodFiniteReconstruction_measurable_completion20261011 selection).aemeasurable)) :=
  ProbabilityMeasure.tendsto_map_of_tendsto_of_continuous laws law convergence
    (skorokhodFiniteReconstruction_lipschitz_completion20261011 selection).continuous

theorem skorokhod_reconstruction_modulus_bound_completion20261011 {count : ℕ}
    (coordinates : Fin count → SkorokhodIntervalTimeCompletion20261011)
    (selection : SkorokhodIntervalTimeCompletion20261011 → Fin count)
    (path : SkorokhodIntervalPathCompletion20261011 Space)
    (duration tolerance : ℝ)
    (near : ∀ time, dist time (coordinates (selection time)) < duration)
    (modulus : ∀ first second, dist first second < duration → dist (path first) (path second) ≤ tolerance) :
    edist path (skorokhodFiniteReconstructionCompletion20261011 selection (fun index => path (coordinates index))) ≤ ENNReal.ofReal tolerance := by
  apply (skorokhodJ1EDist_le_uniform_completion20261011 _ _).trans
  apply iSup_le
  intro time
  rw [edist_dist]
  exact ENNReal.ofReal_le_ofReal (modulus time (coordinates (selection time)) (near time))

theorem skorokhodJ1EDist_ne_top_completion20261011 [CompactSpace Space]
    (first second : SkorokhodIntervalPathCompletion20261011 Space) : edist first second ≠ ⊤ := by
  have bound : edist first second ≤ ENNReal.ofReal (Metric.diam (Set.univ : Set Space)) := by
    apply (skorokhodJ1EDist_le_uniform_completion20261011 _ _).trans
    apply iSup_le
    intro time
    rw [edist_dist]
    exact ENNReal.ofReal_le_ofReal (Metric.dist_le_diam_of_mem isCompact_univ.isBounded (mem_univ _) (mem_univ _))
  exact ne_top_of_le_ne_top ENNReal.ofReal_ne_top bound

instance skorokhodJ1PseudoMetricCompletion20261011 [CompactSpace Space] :
    PseudoMetricSpace (SkorokhodIntervalPathCompletion20261011 Space) :=
  PseudoEMetricSpace.toPseudoMetricSpace skorokhodJ1EDist_ne_top_completion20261011

end
end IGSIII34.Diffusion

