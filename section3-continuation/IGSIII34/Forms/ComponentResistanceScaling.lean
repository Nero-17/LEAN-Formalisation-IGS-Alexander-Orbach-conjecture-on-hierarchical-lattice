import IGSIII34.ResistanceLimit.RetainedWordEnergy
import IGSIII34.ResistanceLimit.StationaryGeneration

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
namespace IGSIII34.Forms
noncomputable section
open Universality Universality.FiniteNetwork IGSIII34.Percolation IGSIII34.ResistanceLimit
open IGSIII.Chemical.Substitution IGSIII.Geometry

theorem generationEdgeAddress_componentWord (rule : Rule) (fine age : ℕ)
    (word : Fin age → Fin rule.edges) (edge : Fin (rule.generation fine).edges) :
    generationEdgeAddress rule (fine + age)
      ((generationComponentWordEmbedding rule fine age word).edge edge) =
        List.ofFn word ++ generationEdgeAddress rule fine edge := by
  induction age with
  | zero =>
    simp only [generationComponentWordEmbedding, NetworkEmbedding.refl, List.ofFn_zero, List.nil_append]
    rfl
  | succ age previous =>
    change generationEdgeAddress rule ((fine + age) + 1)
      ((rule.generationTopDecomposition (fine + age)).edge.symm
        (finProdFinEquiv (word 0, (generationComponentWordEmbedding rule fine age (fun index => word index.succ)).edge edge))) = _
    rw [generationEdgeAddress_top, previous]
    simp only [List.ofFn_succ, List.cons_append]

theorem stationary_component_resistance_scaling (rule : Rule)
    (field : List (Fin rule.edges) → ℝ) (growth : ℝ) (fine age : ℕ)
    (word : Fin age → (Fin rule.edges × Bool)) (edge : Fin (rule.generation fine).edges) :
    stationaryGenerationResistance rule field growth (fine + age) []
      ((generationComponentWordEmbedding rule fine age (fun index => (word index).1)).edge edge) =
        growth⁻¹ ^ age * stationaryGenerationResistance rule field growth fine
          (componentEdgeAddress (List.ofFn word)) edge := by
  unfold stationaryGenerationResistance
  rw [generationEdgeAddress_componentWord]
  simp only [List.nil_append, componentEdgeAddress, List.map_ofFn, Function.comp_def]
  rw [show fine + age + 1 = age + (fine + 1) by omega, pow_add]
  ring

theorem stationary_component_conductance_scaling (rule : Rule)
    (field : List (Fin rule.edges) → ℝ) (growth : ℝ) (fine age : ℕ)
    (word : Fin age → (Fin rule.edges × Bool)) (edge : Fin (rule.generation fine).edges) :
    (stationaryGenerationResistance rule field growth (fine + age) []
      ((generationComponentWordEmbedding rule fine age (fun index => (word index).1)).edge edge))⁻¹ =
        growth ^ age * (stationaryGenerationResistance rule field growth fine
          (componentEdgeAddress (List.ofFn word)) edge)⁻¹ := by
  rw [stationary_component_resistance_scaling, mul_inv_rev, inv_pow, inv_inv, mul_comm]

end
end IGSIII34.Forms
