import IGSIII.Chemical.SmallBall.FiniteComponentOwnership
import Mathlib.Probability.UniformOn

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace IGSIII.Geometry
noncomputable section

open MeasureTheory ProbabilityTheory Classical

variable {Index Source : Type*} {Child : Index → Type*}
variable [Fintype Index] [Fintype Source] [∀ index, Fintype (Child index)] [Nonempty Source]
variable [MeasurableSpace Index] [MeasurableSingletonClass Index]
variable [MeasurableSpace Source] [MeasurableSingletonClass Source]

theorem uniformOn_univ_finset (event : Finset Source) :
    uniformOn (Set.univ : Set Source) event = ENNReal.ofReal ((event.card : ℝ) / Fintype.card Source) := by
  classical
  rw [← Finset.coe_univ, uniformOn_apply_finset]
  simp only [Finset.univ_inter, Finset.card_univ]
  rw [ENNReal.ofReal_div_of_pos (by exact_mod_cast Fintype.card_pos)]
  simp

theorem finite_uniform_ownership_singleton (embedding : (Σ index, Child index) ↪ Source)
    (fallback index : Index) :
    (uniformOn (Set.univ : Set Source)).map (finiteComponentOwnership embedding fallback) {index} =
      ENNReal.ofReal (((Fintype.card (Child index) +
        if index = fallback then (finiteComponentFrontier embedding).card else 0 : ℕ) : ℝ) / Fintype.card Source) := by
  classical
  rw [Measure.map_apply (measurable_of_finite _) (measurableSet_singleton index)]
  have event : (finiteComponentOwnership embedding fallback) ⁻¹' {index} =
      (Finset.univ.filter (fun point => finiteComponentOwnership embedding fallback point = index) : Set Source) := by
    ext point
    simp
  rw [event, uniformOn_univ_finset, finiteComponentOwnership_fiber_card]

theorem finite_uniform_frontier_mass (embedding : (Σ index, Child index) ↪ Source) :
    uniformOn (Set.univ : Set Source) (finiteComponentFrontier embedding) =
      ENNReal.ofReal (((finiteComponentFrontier embedding).card : ℝ) / Fintype.card Source) :=
  uniformOn_univ_finset _

end
end IGSIII.Geometry
