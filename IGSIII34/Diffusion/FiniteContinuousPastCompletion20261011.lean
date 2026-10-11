import Mathlib.Probability.Process.Filtration
import Mathlib.MeasureTheory.Function.LpSpace.ContinuousFunctions

/-! Actual finite continuous past observations are measurable in the
full discrete past filtration and square integrable, uniformly in the
spatial placement and the observation times. -/
set_option autoImplicit false
set_option maxHeartbeats 2400000
namespace IGSIII34.Diffusion
noncomputable section
open MeasureTheory ProbabilityTheory Preorder Filter
open scoped Topology
variable {Vertex Space : Type*} [MeasurableSpace Vertex]
  [TopologicalSpace Space] [CompactSpace Space] [SecondCountableTopology Space] [MeasurableSpace Space] [BorelSpace Space]

def finiteContinuousPastCompletion20261011 {count : ℕ}
    (test : C(Fin count → Space, ℝ)) (coordinates : Fin count → ℕ)
    (inclusion : Vertex → Space) (path : ℕ → Vertex) : ℝ :=
  test (fun index => inclusion (path (coordinates index)))

theorem finiteContinuousPast_known_completion20261011 {count : ℕ}
    (test : C(Fin count → Space, ℝ)) (coordinates : Fin count → ℕ)
    (inclusion : Vertex → Space) (inclusionMeasurable : Measurable inclusion)
    (time : ℕ) (before : ∀ index, coordinates index ≤ time) :
    StronglyMeasurable[Filtration.piLE (X := fun _ : ℕ => Vertex) time]
      (finiteContinuousPastCompletion20261011 test coordinates inclusion) := by
  rw [Filtration.piLE_eq_comap_frestrictLe]
  have observationMeasurable : Measurable (fun history : Finset.Iic time → Vertex =>
      fun index : Fin count => inclusion (history ⟨coordinates index, Finset.mem_Iic.mpr (before index)⟩)) := by
    apply measurable_pi_lambda
    intro index
    exact inclusionMeasurable.comp (measurable_pi_apply _)
  exact (test.continuous.stronglyMeasurable.comp_measurable observationMeasurable).comp_measurable
    (Measurable.of_comap_le le_rfl)

theorem finiteContinuousPast_memLp_completion20261011 {count : ℕ}
    (law : Measure (ℕ → Vertex)) [IsFiniteMeasure law]
    (test : C(Fin count → Space, ℝ)) (coordinates : Fin count → ℕ)
    (inclusion : Vertex → Space) (inclusionMeasurable : Measurable inclusion)
    (power : ENNReal) :
    MemLp (finiteContinuousPastCompletion20261011 test coordinates inclusion) power law := by
  have observationMeasurable : Measurable (fun path : ℕ → Vertex =>
      fun index : Fin count => inclusion (path (coordinates index))) := by
    apply measurable_pi_lambda
    intro index
    exact inclusionMeasurable.comp (measurable_pi_apply _)
  apply MemLp.of_bound (test.continuous.stronglyMeasurable.comp_measurable observationMeasurable).aestronglyMeasurable ‖test‖
  exact Eventually.of_forall (fun path => ContinuousMap.norm_coe_le_norm test _)

end
end IGSIII34.Diffusion

