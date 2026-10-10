import IGSIII34.ResistanceLimit.Rayleigh
import IGSIII.Geometry.ActualSkeletonVertices

set_option autoImplicit false
set_option maxHeartbeats 1800000
namespace IGSIII34.ResistanceLimit
noncomputable section
open Universality Universality.FiniteNetwork IGSIII34.Percolation
open IGSIII.Chemical.Substitution IGSIII.Geometry

theorem networkEmbedding_unit_pairResistance_le
    {childVertices childEdges parentVertices parentEdges : ℕ}
    {child : Universality.FiniteNetwork childVertices childEdges}
    {parent : Universality.FiniteNetwork parentVertices parentEdges}
    (embedding : child.NetworkEmbedding parent) (configuration : Configuration parentEdges)
    (first last : Fin childVertices)
    (reachable : (child.openGraph (embedding.restrict configuration)).Reachable first last) :
    pairResistance (network parent configuration) (fun _ => 1)
      (embedding.vertex first) (embedding.vertex last) ≤
      pairResistance (network child (embedding.restrict configuration)) (fun _ => 1) first last := by
  let edges : {edge : Fin childEdges // embedding.restrict configuration edge = true} ↪
      {edge : Fin parentEdges // configuration edge = true} :=
    ⟨fun edge => ⟨embedding.edge edge.val, edge.property⟩, by
      intro first last equality
      exact Subtype.ext (embedding.edge.injective (congrArg Subtype.val equality))⟩
  exact embedded_pairResistance_le (network child (embedding.restrict configuration)) (network parent configuration)
    embedding.vertex edges (fun edge => embedding.endpoint edge.val)
    (fun _ => 1) (fun _ => 1) (fun _ => zero_lt_one) (fun _ => zero_lt_one) (fun _ => rfl)
    first last (by rwa [graph_eq_openGraph])

theorem markedChild_pairResistance_le (rule : Rule)
    (marks : (List (Fin rule.edges) × Bool) → Configuration rule.edges)
    (depth : ℕ) (address : List (Fin rule.edges)) (opened : Bool) (edge : Fin rule.edges)
    (first last : Fin (rule.generation depth).vertices)
    (reachable : ((rule.generation depth).network.openGraph
      (markedGenerationConfiguration rule marks depth (address ++ [edge]) (marks (address, opened) edge))).Reachable first last) :
    pairResistance (network (rule.generation (depth + 1)).network
      (markedGenerationConfiguration rule marks (depth + 1) address opened)) (fun _ => 1)
      ((rule.generationCellEmbedding depth edge).vertex first) ((rule.generationCellEmbedding depth edge).vertex last) ≤
    pairResistance (network (rule.generation depth).network
      (markedGenerationConfiguration rule marks depth (address ++ [edge]) (marks (address, opened) edge)))
      (fun _ => 1) first last := by
  have childReach : ((rule.generation depth).network.openGraph
      ((rule.generationCellEmbedding depth edge).restrict
        (markedGenerationConfiguration rule marks (depth + 1) address opened))).Reachable first last := by
    rwa [generationCellEmbedding_restrict_marked]
  have comparison := networkEmbedding_unit_pairResistance_le (rule.generationCellEmbedding depth edge)
    (markedGenerationConfiguration rule marks (depth + 1) address opened) first last childReach
  exact comparison.trans_eq (congrArg (fun configuration : Configuration (rule.generation depth).edges =>
    pairResistance (network (rule.generation depth).network configuration) (fun _ => 1) first last)
      (generationCellEmbedding_restrict_marked rule marks depth address opened edge))

theorem normalized_markedChild_pairResistance_le (rule : Rule)
    (marks : (List (Fin rule.edges) × Bool) → Configuration rule.edges)
    (depth : ℕ) (address : List (Fin rule.edges)) (opened : Bool) (edge : Fin rule.edges)
    (first last : Fin (rule.generation depth).vertices)
    (reachable : ((rule.generation depth).network.openGraph
      (markedGenerationConfiguration rule marks depth (address ++ [edge]) (marks (address, opened) edge))).Reachable first last)
    (scale : ℝ) (scalePositive : 0 < scale) :
    pairResistance (network (rule.generation (depth + 1)).network
      (markedGenerationConfiguration rule marks (depth + 1) address opened)) (fun _ => 1)
      ((rule.generationCellEmbedding depth edge).vertex first) ((rule.generationCellEmbedding depth edge).vertex last) /
        scale ^ (depth + 1 + 1 + address.length) ≤
    pairResistance (network (rule.generation depth).network
      (markedGenerationConfiguration rule marks depth (address ++ [edge]) (marks (address, opened) edge)))
      (fun _ => 1) first last / scale ^ (depth + 1 + (address ++ [edge]).length) := by
  have lengths : depth + 1 + 1 + address.length = depth + 1 + (address ++ [edge]).length := by simp; omega
  rw [lengths]
  exact div_le_div_of_nonneg_right (markedChild_pairResistance_le rule marks depth address opened edge first last reachable)
    (pow_pos scalePositive _).le

end
end IGSIII34.ResistanceLimit
