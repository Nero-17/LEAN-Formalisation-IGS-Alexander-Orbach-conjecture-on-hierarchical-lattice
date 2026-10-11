import IGSIII34.Diffusion.DistanceProfileEmbedding
import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.MeasureTheory.Function.SpecialFunctions.Basic

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace IGSIII34.Diffusion
noncomputable section
open Filter Set MeasureTheory
open scoped Topology ENNReal

/-- Recover the original distance coordinates, rather than the auxiliary
compact product metric. The zero-coordinate convention is used only away
from actual distance profiles. -/
def distanceProfileDecodedCoordinate {Labels : Type*}
    (profile : CountableDistanceProfile Labels) (label : Labels) : ℝ :=
  -Real.log (profile label : ℝ)

def distanceProfileOriginalEDist {Labels : Type*}
    (first last : CountableDistanceProfile Labels) : ℝ≥0∞ :=
  ⨆ label, edist (distanceProfileDecodedCoordinate first label)
    (distanceProfileDecodedCoordinate last label)

theorem distanceProfileDecodedCoordinate_actual {Labels Space : Type*}
    [MetricSpace Space] (births : Labels → Space) (point : Space) (label : Labels) :
    distanceProfileDecodedCoordinate (distanceProfilePoint births point) label =
      dist point (births label) := by
  simp [distanceProfileDecodedCoordinate, distanceProfilePoint, Real.log_exp]

theorem distanceProfileOriginalEDist_actual {Labels Space : Type*}
    [MetricSpace Space] (births : Labels → Space) (dense : DenseRange births)
    (first last : Space) :
    distanceProfileOriginalEDist (distanceProfilePoint births first)
      (distanceProfilePoint births last) = edist first last := by
  simp only [distanceProfileOriginalEDist, distanceProfileDecodedCoordinate_actual]
  apply le_antisymm
  · apply iSup_le
    intro label
    rw [edist_dist, edist_dist]
    apply ENNReal.ofReal_le_ofReal
    simpa only [Real.dist_eq] using abs_dist_sub_le first last (births label)
  · have upper : (⨆ label, edist (dist first (births label))
        (dist last (births label))) ≤ edist first last := by
      apply iSup_le
      intro label
      rw [edist_dist, edist_dist]
      apply ENNReal.ofReal_le_ofReal
      simpa only [Real.dist_eq] using abs_dist_sub_le first last (births label)
    have finite : (⨆ label, edist (dist first (births label))
        (dist last (births label))) ≠ ∞ := ne_top_of_le_ne_top (edist_ne_top first last) upper
    rw [edist_dist, ENNReal.ofReal_le_iff_le_toReal finite]
    apply le_of_forall_pos_le_add
    intro tolerance positive
    obtain ⟨label, close⟩ := Metric.mem_closure_range_iff.mp (dense first)
      (tolerance / 2) (half_pos positive)
    have coordinate := le_iSup (fun label => edist (dist first (births label))
      (dist last (births label))) label
    rw [edist_dist] at coordinate
    have coordinateReal := ENNReal.toReal_mono finite coordinate
    rw [ENNReal.toReal_ofReal dist_nonneg, Real.dist_eq] at coordinateReal
    have triangle := dist_triangle first (births label) last
    rw [dist_comm (births label) last] at triangle
    have difference := le_abs_self (dist last (births label) - dist first (births label))
    rw [abs_sub_comm] at coordinateReal
    linarith

theorem distanceProfileDecodedCoordinate_measurable {Labels : Type*}
    [Countable Labels] (label : Labels) :
    Measurable (fun profile : CountableDistanceProfile Labels =>
      distanceProfileDecodedCoordinate profile label) := by
  have evaluation : Continuous (fun profile : CountableDistanceProfile Labels =>
      (profile label : ℝ)) := continuous_subtype_val.comp (continuous_apply label)
  have evaluationMeasurable : Measurable (fun profile : CountableDistanceProfile Labels =>
      (profile label : ℝ)) := evaluation.measurable
  exact (Real.measurable_log.comp evaluationMeasurable).neg

theorem distanceProfileOriginalEDist_measurable {Labels : Type*}
    [Countable Labels] :
    Measurable (fun pair : CountableDistanceProfile Labels × CountableDistanceProfile Labels =>
      distanceProfileOriginalEDist pair.1 pair.2) := by
  apply Measurable.iSup
  intro label
  exact ((distanceProfileDecodedCoordinate_measurable label).comp measurable_fst).edist
    ((distanceProfileDecodedCoordinate_measurable label).comp measurable_snd)

end
end IGSIII34.Diffusion
