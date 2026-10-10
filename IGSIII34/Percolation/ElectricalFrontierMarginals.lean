import IGSIII34.Percolation.ElectricalPrefix
import IGSIII.Probability.IndependentFrontier

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
namespace IGSIII34.Percolation
noncomputable section
open Universality Universality.FiniteNetwork MeasureTheory ProbabilityTheory
open IGSIII.Probability IGSIII.Chemical.Substitution

theorem generationFrontier_measurable (rule : Rule) (depth : ℕ) :
    Measurable (fun marks (leaf : Fin (rule.generation depth).edges) =>
      innovationTreeShift rule (generationEdgeAddress rule depth leaf) marks) :=
  measurable_pi_lambda _ (fun leaf => innovationTreeShift_measurable rule (generationEdgeAddress rule depth leaf))

theorem generationFrontier_eval_preserving (rule : Rule)
    (p : ℝ) (positive : 0 < p) (belowOne : p < 1) (fixedPoint : rule.network.reliability p = p)
    (depth : ℕ) (leaf : Fin (rule.generation depth).edges) :
    MeasurePreserving (fun children : Fin (rule.generation depth).edges →
        ((List (Fin rule.edges) × Bool) → Configuration rule.edges) => children leaf)
      ((independentInnovationLaw rule p positive belowOne fixedPoint).map
        (fun marks (leaf : Fin (rule.generation depth).edges) => innovationTreeShift rule (generationEdgeAddress rule depth leaf) marks))
      (independentInnovationLaw rule p positive belowOne fixedPoint) := by
  refine ⟨measurable_pi_apply leaf, ?_⟩
  rw [Measure.map_map (measurable_pi_apply leaf) (generationFrontier_measurable rule depth)]
  exact (innovationTreeShift_preserving rule p positive belowOne fixedPoint (generationEdgeAddress rule depth leaf)).map_eq

theorem generationFrontier_eval_integral (rule : Rule)
    (p : ℝ) (positive : 0 < p) (belowOne : p < 1) (fixedPoint : rule.network.reliability p = p)
    (depth : ℕ) (leaf : Fin (rule.generation depth).edges)
    (response : ((List (Fin rule.edges) × Bool) → Configuration rule.edges) → ℝ)
    (measurable : StronglyMeasurable response) :
    (∫ children : Fin (rule.generation depth).edges → ((List (Fin rule.edges) × Bool) → Configuration rule.edges),
        response (children leaf) ∂(independentInnovationLaw rule p positive belowOne fixedPoint).map
          (fun marks (leaf : Fin (rule.generation depth).edges) => innovationTreeShift rule (generationEdgeAddress rule depth leaf) marks)) =
      ∫ marks, response marks ∂independentInnovationLaw rule p positive belowOne fixedPoint := by
  have mapped := integral_map_of_stronglyMeasurable
    (μ := (independentInnovationLaw rule p positive belowOne fixedPoint).map
      (fun marks (leaf : Fin (rule.generation depth).edges) => innovationTreeShift rule (generationEdgeAddress rule depth leaf) marks))
    (φ := fun children : Fin (rule.generation depth).edges → ((List (Fin rule.edges) × Bool) → Configuration rule.edges) => children leaf)
    (measurable_pi_apply leaf) measurable
  have preserving := generationFrontier_eval_preserving rule p positive belowOne fixedPoint depth leaf
  rw [preserving.map_eq] at mapped
  exact mapped.symm

theorem generationFrontier_eval_independent (rule : Rule)
    (p : ℝ) (positive : 0 < p) (belowOne : p < 1) (fixedPoint : rule.network.reliability p = p)
    (depth : ℕ) :
    iIndepFun (fun (leaf : Fin (rule.generation depth).edges)
        (children : Fin (rule.generation depth).edges → ((List (Fin rule.edges) × Bool) → Configuration rule.edges)) => children leaf)
      ((independentInnovationLaw rule p positive belowOne fixedPoint).map
        (fun marks (leaf : Fin (rule.generation depth).edges) => innovationTreeShift rule (generationEdgeAddress rule depth leaf) marks)) := by
  rw [innovationFrontier_map rule p positive belowOne fixedPoint (generationEdgeAddress rule depth)
    (generationEdgeAddress_injective rule depth) (depth+1) (generationEdgeAddress_length rule depth)]
  exact iIndepFun_infinitePi (X := fun _ value => value) (fun _ => measurable_id)

end
end IGSIII34.Percolation

