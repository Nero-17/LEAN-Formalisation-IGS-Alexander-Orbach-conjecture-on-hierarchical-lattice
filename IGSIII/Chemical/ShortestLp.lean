import IGSIII.Chemical.PathFunctional
import Mathlib.MeasureTheory.Function.LpSpace.Basic
import Mathlib.MeasureTheory.Function.LpSeminorm.TriangleInequality
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic

set_option autoImplicit false

namespace IGSIII.Chemical.PathFamily

open MeasureTheory
open scoped ENNReal

variable {Edge : Type*} [Fintype Edge] [DecidableEq Edge]

theorem shortest_lipschitzWith (family : PathFamily Edge) :
    LipschitzWith (Fintype.card Edge) family.shortest := by
  apply LipschitzWith.of_dist_le_mul
  intro first second
  rw [Real.dist_eq]
  calc
    _ ≤ ∑ edge, |first edge - second edge| := family.shortest_lipschitz first second
    _ ≤ ∑ _edge : Edge, dist first second := by
      apply Finset.sum_le_sum
      intro edge _
      exact dist_le_pi_dist first second edge
    _ = _ := by simp

theorem shortest_continuous (family : PathFamily Edge) : Continuous family.shortest :=
  family.shortest_lipschitzWith.continuous

theorem shortest_measurable (family : PathFamily Edge) : Measurable family.shortest :=
  family.shortest_continuous.measurable

theorem shortest_abs_le (family : PathFamily Edge) (cost : Edge → ℝ) :
    |family.shortest cost| ≤ ∑ edge, |cost edge| := by
  simpa using family.shortest_lipschitz cost (fun _ => 0)

variable {Sample State : Type*} [MeasurableSpace Sample] [MeasurableSpace State]
    [Countable State] [MeasurableSingletonClass State]
    (families : State → PathFamily Edge)

theorem shortest_dispatch_measurable :
    Measurable (fun input : State × (Edge → ℝ) => (families input.1).shortest input.2) :=
  measurable_from_prod_countable_right (fun state => (families state).shortest_measurable)

theorem shortest_random_memLp {measure : Measure Sample} {order : ℝ≥0∞}
    {state : Sample → State} (stateMeasurable : AEMeasurable state measure)
    {cost : Edge → Sample → ℝ} (costIntegrable : ∀ edge, MemLp (cost edge) order measure) :
    MemLp (fun sample => (families (state sample)).shortest (fun edge => cost edge sample))
      order measure := by
  have measurable : AEStronglyMeasurable
      (fun sample => (families (state sample)).shortest (fun edge => cost edge sample)) measure :=
    ((shortest_dispatch_measurable families).comp_aemeasurable
      (stateMeasurable.prodMk (aemeasurable_pi_lambda _ (fun edge =>
        (costIntegrable edge).aestronglyMeasurable.aemeasurable)))).aestronglyMeasurable
  have envelope : MemLp (fun sample => ∑ edge, ‖cost edge sample‖) order measure :=
    memLp_finsetSum _ (fun edge _ => (costIntegrable edge).norm)
  exact envelope.mono' measurable (Filter.Eventually.of_forall (fun sample => by
    simpa using (families (state sample)).shortest_abs_le (fun edge => cost edge sample)))

end IGSIII.Chemical.PathFamily

