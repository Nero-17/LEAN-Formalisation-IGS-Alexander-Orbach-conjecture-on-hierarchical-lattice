import IGSIII34.Diffusion.SkorokhodJ1TopologyCompletion
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

instance skorokhodJ1MeasurableCompletion :
    MeasurableSpace (SkorokhodIntervalPathCompletion Space) := borel _
instance skorokhodJ1BorelCompletion :
    BorelSpace (SkorokhodIntervalPathCompletion Space) := ⟨rfl⟩

def skorokhodFiniteReconstructionCompletion {count : ℕ}
    (selection : SkorokhodIntervalTimeCompletion → Fin count)
    (values : Fin count → Space) : SkorokhodIntervalPathCompletion Space :=
  ⟨fun time => values (selection time)⟩

theorem skorokhodFiniteReconstruction_lipschitz_completion {count : ℕ}
    (selection : SkorokhodIntervalTimeCompletion → Fin count) :
    LipschitzWith 1 (skorokhodFiniteReconstructionCompletion (Space := Space) selection) := by
  apply LipschitzWith.of_edist_le
  intro first second
  apply (skorokhodJ1EDist_le_uniform_completion _ _).trans
  apply iSup_le
  intro time
  exact edist_le_pi_edist first second (selection time)

theorem skorokhodFiniteReconstruction_measurable_completion
    [MeasurableSpace Space] [BorelSpace Space] [SecondCountableTopology Space] {count : ℕ}
    (selection : SkorokhodIntervalTimeCompletion → Fin count) :
    Measurable (skorokhodFiniteReconstructionCompletion (Space := Space) selection) :=
  (skorokhodFiniteReconstruction_lipschitz_completion selection).continuous.measurable

theorem skorokhod_reconstructed_sample_measurable_completion
    [MeasurableSpace Space] [BorelSpace Space] [SecondCountableTopology Space]
    {Outcome : Type*} [MeasurableSpace Outcome] {count : ℕ}
    (selection : SkorokhodIntervalTimeCompletion → Fin count)
    (sample : Outcome → Fin count → Space) (sampleMeasurable : Measurable sample) :
    Measurable (fun outcome => skorokhodFiniteReconstructionCompletion selection (sample outcome)) :=
  (skorokhodFiniteReconstruction_measurable_completion selection).comp sampleMeasurable

theorem skorokhod_reconstruction_weak_convergence_completion
    [MeasurableSpace Space] [BorelSpace Space] [SecondCountableTopology Space] {count : ℕ}
    (selection : SkorokhodIntervalTimeCompletion → Fin count)
    (laws : ℕ → ProbabilityMeasure (Fin count → Space))
    (law : ProbabilityMeasure (Fin count → Space)) (convergence : Tendsto laws atTop (𝓝 law)) :
    Tendsto (fun index => (laws index).map (skorokhodFiniteReconstruction_measurable_completion selection).aemeasurable)
      atTop (𝓝 (law.map (skorokhodFiniteReconstruction_measurable_completion selection).aemeasurable)) :=
  ProbabilityMeasure.tendsto_map_of_tendsto_of_continuous laws law convergence
    (skorokhodFiniteReconstruction_lipschitz_completion selection).continuous

theorem skorokhod_reconstruction_modulus_bound_completion {count : ℕ}
    (coordinates : Fin count → SkorokhodIntervalTimeCompletion)
    (selection : SkorokhodIntervalTimeCompletion → Fin count)
    (path : SkorokhodIntervalPathCompletion Space)
    (duration tolerance : ℝ)
    (near : ∀ time, dist time (coordinates (selection time)) < duration)
    (modulus : ∀ first second, dist first second < duration → dist (path first) (path second) ≤ tolerance) :
    edist path (skorokhodFiniteReconstructionCompletion selection (fun index => path (coordinates index))) ≤ ENNReal.ofReal tolerance := by
  apply (skorokhodJ1EDist_le_uniform_completion _ _).trans
  apply iSup_le
  intro time
  rw [edist_dist]
  exact ENNReal.ofReal_le_ofReal (modulus time (coordinates (selection time)) (near time))

theorem skorokhodJ1EDist_ne_top_completion [CompactSpace Space]
    (first second : SkorokhodIntervalPathCompletion Space) : edist first second ≠ ⊤ := by
  have bound : edist first second ≤ ENNReal.ofReal (Metric.diam (Set.univ : Set Space)) := by
    apply (skorokhodJ1EDist_le_uniform_completion _ _).trans
    apply iSup_le
    intro time
    rw [edist_dist]
    exact ENNReal.ofReal_le_ofReal (Metric.dist_le_diam_of_mem isCompact_univ.isBounded (mem_univ _) (mem_univ _))
  exact ne_top_of_le_ne_top ENNReal.ofReal_ne_top bound

instance skorokhodJ1PseudoMetricCompletion [CompactSpace Space] :
    PseudoMetricSpace (SkorokhodIntervalPathCompletion Space) :=
  PseudoEMetricSpace.toPseudoMetricSpace skorokhodJ1EDist_ne_top_completion

end
end IGSIII34.Diffusion

