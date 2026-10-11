import IGSIII34.Forms.ComponentResistanceScaling
import IGSIII34.Forms.ComponentEnergyDecomposition
import IGSIII34.ResistanceLimit.SelectedComponentEnergy

set_option autoImplicit false
set_option maxHeartbeats 2600000
set_option backward.isDefEq.respectTransparency false
namespace IGSIII34.Forms
noncomputable section
open Universality Universality.FiniteNetwork IGSIII34.Percolation IGSIII34.ResistanceLimit IGSIII34.Diffusion
open IGSIII.Chemical.Substitution IGSIII.Geometry
open scoped BigOperators

/-- A genuine retained component's globally normalized energy is its
intrinsic energy multiplied by the electrical scale at its birth depth.
The identity keeps the inherited side mask, including both B components. -/
theorem retainedWordTraceEnergy_stationary_scaling (rule : Rule)
    (marks : (List (Fin rule.edges) × Bool) → Configuration rule.edges)
    (crossing : ∀ address opened, rule.network.crosses (marks (address, opened)) = opened)
    (field : List (Fin rule.edges) → ℝ) (growth : ℝ) (fine age : ℕ)
    (potential : Fin (rule.generation (fine + age)).vertices → ℝ)
    (word : Fin age → (Fin rule.edges × Bool)) :
    retainedWordTraceEnergy rule marks crossing fine age
      (fun edge => stationaryGenerationResistance rule field growth (fine + age) [] edge.val) potential word =
      growth ^ age * selectedComponentTraceEnergy rule marks fine (List.ofFn word)
        (fun edge => stationaryGenerationResistance rule field growth fine
          (componentEdgeAddress (List.ofFn word)) edge.val)
        (potential ∘ (generationComponentWordEmbedding rule fine age (fun index => (word index).1)).vertex) := by
  classical
  rw [selectedComponentTraceEnergy_eq_sum rule marks crossing, Finset.mul_sum]
  unfold retainedWordTraceEnergy
  apply Finset.sum_congr rfl
  intro edge _
  have edgeIdentity : (actualComponentEdgeEmbedding rule marks crossing fine age ⟨word, edge⟩).val =
      (generationComponentWordEmbedding rule fine age (fun index => (word index).1)).edge edge.val := by
    change (selectedComponentWordEdgeEmbedding rule marks crossing fine age [] .connected ⟨word, edge⟩).val = _
    exact selectedComponentWordEdgeEmbedding_edge rule marks crossing fine age [] .connected ⟨word, edge⟩
  dsimp only
  rw [edgeIdentity, stationary_component_conductance_scaling,
    (generationComponentWordEmbedding rule fine age (fun index => (word index).1)).endpoint]
  simp only [Function.comp_apply, Prod.map_fst, Prod.map_snd, mul_assoc]

end
end IGSIII34.Forms
