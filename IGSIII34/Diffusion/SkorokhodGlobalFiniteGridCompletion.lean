import IGSIII34.Diffusion.SkorokhodGlobalTopologyCompletion
import IGSIII34.Diffusion.PathWeakReconstructionCompletion
import Mathlib.Topology.Algebra.InfiniteSum.Real

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3200000
namespace IGSIII34.Diffusion
noncomputable section
open MeasureTheory Filter Set
open scoped _root_.Topology NNReal ENNReal
variable {Space : Type*} [MetricSpace Space] [CompactSpace Space]

theorem skorokhodGlobal_dist_eq_tsum_completion
    (first second : SkorokhodGlobalPathCompletion Space) :
    dist first second = ∑' index : ℕ, min ((2 : ℝ)⁻¹ ^ index)
      (dist (skorokhodIntegerProfileCompletion first index)
        (skorokhodIntegerProfileCompletion second index)) := by
  rfl

/-- A finite collection of genuine J1 controls bounds the whole path
distance, with an explicit summable tail independent of both paths. -/
theorem skorokhodGlobal_dist_finite_profile_bound_completion
    (first second : SkorokhodGlobalPathCompletion Space)
    (count : ℕ) (tolerance : ℝ)
    (bounds : ∀ index < count, dist (skorokhodIntegerProfileCompletion first index)
      (skorokhodIntegerProfileCompletion second index) ≤ tolerance) :
    dist first second ≤ count * tolerance + 2 * (2 : ℝ)⁻¹ ^ count := by
  let terms := fun index : ℕ => min ((2 : ℝ)⁻¹ ^ index)
    (dist (skorokhodIntegerProfileCompletion first index)
      (skorokhodIntegerProfileCompletion second index))
  have summableTerms : Summable terms :=
    PiCountable.dist_summable (skorokhodIntegerProfileCompletion first)
      (skorokhodIntegerProfileCompletion second)
  rw [skorokhodGlobal_dist_eq_tsum_completion,
    ← Summable.sum_add_tsum_nat_add count summableTerms]
  apply add_le_add
  · calc
      ∑ index ∈ Finset.range count, terms index ≤
          ∑ index ∈ Finset.range count, tolerance := Finset.sum_le_sum fun index belongs =>
        (min_le_right _ _).trans (bounds index (Finset.mem_range.mp belongs))
      _ = count * tolerance := by simp
  · have tailSummable : Summable (fun index : ℕ => terms (index+count)) :=
      summableTerms.comp_injective (by intro first second same; change first+count = second+count at same; omega)
    have inverseSummable : Summable (fun index : ℕ => (2 : ℝ)⁻¹ ^ index) := by
      simpa only [one_div] using summable_geometric_two
    have geometricSummable : Summable (fun index : ℕ => (2 : ℝ)⁻¹ ^ (index+count)) := by
      simpa only [pow_add] using
        inverseSummable.mul_right ((2 : ℝ)⁻¹ ^ count)
    calc
      ∑' index : ℕ, terms (index+count) ≤ ∑' index : ℕ, (2 : ℝ)⁻¹ ^ (index+count) :=
        tailSummable.tsum_le_tsum (fun _ => min_le_left _ _) geometricSummable
      _ = 2 * (2 : ℝ)⁻¹ ^ count := by
        simp only [pow_add, tsum_mul_right, tsum_geometric_inv_two]

def skorokhodGlobalFiniteReconstructionCompletion {count : ℕ}
    (selection : ℝ≥0 → Fin count) (values : Fin count → Space) :
    SkorokhodGlobalPathCompletion Space :=
  ⟨fun time => values (selection time)⟩

theorem skorokhodGlobalFiniteReconstruction_continuous_completion
    {count : ℕ} (selection : ℝ≥0 → Fin count) :
    Continuous (skorokhodGlobalFiniteReconstructionCompletion (Space := Space) selection) := by
  apply skorokhodGlobal_continuous_iff_completion.mpr
  intro horizon
  exact (skorokhodFiniteReconstruction_lipschitz_completion (Space := Space)
    (fun time => selection ((horizon+1 : ℝ≥0) * ⟨time.val, time.property.1⟩))).continuous

theorem skorokhodGlobalFiniteReconstruction_measurable_completion
    [MeasurableSpace Space] [BorelSpace Space] [SecondCountableTopology Space]
    {count : ℕ} (selection : ℝ≥0 → Fin count) :
    Measurable (skorokhodGlobalFiniteReconstructionCompletion (Space := Space) selection) :=
  (skorokhodGlobalFiniteReconstruction_continuous_completion selection).measurable

theorem skorokhodGlobal_reconstruction_weak_completion
    [MeasurableSpace Space] [BorelSpace Space] [SecondCountableTopology Space]
    {count : ℕ} (selection : ℝ≥0 → Fin count)
    (laws : ℕ → ProbabilityMeasure (Fin count → Space))
    (law : ProbabilityMeasure (Fin count → Space)) (convergence : Tendsto laws atTop (𝓝 law)) :
    Tendsto (fun index => (laws index).map
      (skorokhodGlobalFiniteReconstruction_measurable_completion selection).aemeasurable)
      atTop (𝓝 (law.map
        (skorokhodGlobalFiniteReconstruction_measurable_completion selection).aemeasurable)) :=
  ProbabilityMeasure.tendsto_map_of_tendsto_of_continuous laws law convergence
    (skorokhodGlobalFiniteReconstruction_continuous_completion selection)

end
end IGSIII34.Diffusion
