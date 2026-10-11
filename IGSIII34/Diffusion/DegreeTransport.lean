import IGSIII34.Diffusion.FiniteClocks

set_option autoImplicit false
set_option maxHeartbeats 1600000

namespace IGSIII34.Diffusion
noncomputable section
open Universality MeasureTheory ProbabilityTheory Filter
open scoped BigOperators Topology

variable {Vertex Edge Component Space : Type*}
  [Fintype Vertex] [DecidableEq Vertex] [MeasurableSpace Vertex] [MeasurableSingletonClass Vertex]
  [Fintype Edge] [Nonempty Edge]
  [Fintype Component] [DecidableEq Component] [MeasurableSpace Component] [MeasurableSingletonClass Component]
  [MetricSpace Space] [MeasurableSpace Space] [BorelSpace Space]

def halfEndpoint (endpoint : Edge → Vertex × Vertex) (half : Edge × Bool) : Vertex :=
  if half.2 then (endpoint half.1).1 else (endpoint half.1).2

def halfWeight (_half : Edge × Bool) : ℝ := 1 / (2 * Fintype.card Edge)

theorem halfWeight_nonnegative (half : Edge × Bool) : 0 ≤ halfWeight half := by
  unfold halfWeight
  positivity

theorem halfWeight_sum : ∑ half : Edge × Bool, halfWeight half = 1 := by
  simp [halfWeight, Fintype.sum_prod_type, Fintype.sum_bool]
  field_simp
  <;> ring

def halfMeasure [MeasurableSpace (Edge × Bool)] : Measure (Edge × Bool) :=
  (finiteWeightPMF halfWeight halfWeight_nonnegative halfWeight_sum).toMeasure

def degreeMeasure (endpoint : Edge → Vertex × Vertex) : Measure Vertex :=
  (finiteWeightPMF (degreeWeight endpoint) (degreeWeight_nonnegative endpoint)
    (degreeWeight_sum endpoint)).toMeasure

theorem halfEndpoint_weight (endpoint : Edge → Vertex × Vertex) (vertex : Vertex) :
    ∑ half : Edge × Bool, (if halfEndpoint endpoint half = vertex then halfWeight half else 0) =
      degreeWeight endpoint vertex := by
  classical
  simp only [Fintype.sum_prod_type, Fintype.sum_bool, halfEndpoint, Bool.false_eq_true,
    if_false, if_true, halfWeight, degreeWeight, degree]
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro edge _
  split_ifs <;> simp <;> ring

theorem degreeMeasure_eq_half_map (endpoint : Edge → Vertex × Vertex)
    [MeasurableSpace (Edge × Bool)] [MeasurableSingletonClass (Edge × Bool)] :
    degreeMeasure endpoint = (halfMeasure (Edge := Edge)).map (halfEndpoint endpoint) := by
  classical
  apply Measure.ext_of_singleton
  intro vertex
  rw [degreeMeasure, finiteWeightPMF_singleton,
    Measure.map_apply (measurable_of_finite _) (measurableSet_singleton vertex)]
  unfold halfMeasure
  rw [PMF.toMeasure_apply_fintype]
  simp only [Set.indicator, Set.mem_preimage, Set.mem_singleton_iff, finiteWeightPMF_apply]
  have equality := halfEndpoint_weight endpoint vertex
  rw [← equality, ENNReal.ofReal_sum_of_nonneg]
  · apply Finset.sum_congr rfl
    intro half _
    split_ifs <;> simp
  · intro half _
    split_ifs
    · exact halfWeight_nonnegative half
    · exact le_rfl

/-- Assign each edge to one component and move both endpoint half-masses to
that component's anchor. The degree law has exactly the resulting edge-count
weights, with no separate junction error. -/
theorem degree_projection_bound (endpoint : Edge → Vertex × Vertex)
    (inclusion : Vertex → Space) (owner : Edge → Component) (anchor : Component → Space)
    (radius : ℝ) (nonnegative : 0 ≤ radius)
    (close : ∀ edge, dist (inclusion (endpoint edge).1) (anchor (owner edge)) ≤ radius ∧
      dist (inclusion (endpoint edge).2) (anchor (owner edge)) ≤ radius)
    [MeasurableSpace (Edge × Bool)] [MeasurableSingletonClass (Edge × Bool)] :
    levyProkhorovEDist ((degreeMeasure endpoint).map inclusion)
      ((halfMeasure (Edge := Edge)).map (fun half => anchor (owner half.1))) ≤ ENNReal.ofReal radius := by
  rw [degreeMeasure_eq_half_map, Measure.map_map (measurable_of_finite _) (measurable_of_finite _)]
  apply IGSIII.Geometry.levyProkhorovEDist_map_le_of_ae_dist_le
    (halfMeasure (Edge := Edge)) (measurable_of_finite _) (measurable_of_finite _) nonnegative
  apply Filter.Eventually.of_forall
  intro half
  cases half with
  | mk edge side =>
    cases side
    · exact (close edge).2
    · exact (close edge).1

/-- The projected mass of each component is its edge count divided by the
total edge count, even if many edges share an old high-degree vertex. -/
theorem half_owner_weight (owner : Edge → Component) (component : Component) :
    ∑ half : Edge × Bool, (if owner half.1 = component then halfWeight half else 0) =
      ((Finset.univ.filter fun edge => owner edge = component).card : ℝ) / Fintype.card Edge := by
  classical
  simp only [Fintype.sum_prod_type, Fintype.sum_bool, halfWeight]
  rw [Finset.card_eq_sum_ones, Nat.cast_sum, Finset.sum_filter, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro edge _
  split_ifs <;> simp
  <;> field_simp
  <;> ring

end
end IGSIII34.Diffusion
