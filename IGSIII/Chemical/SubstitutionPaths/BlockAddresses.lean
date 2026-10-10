import IGSIII.Chemical.SubstitutionPaths.WeightedGeneration
import IGSIII.Chemical.SubstitutionPaths.CommonPrefix

set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option backward.isDefEq.respectTransparency false

namespace IGSIII.Chemical.Substitution
noncomputable section

open Universality Universality.FiniteNetwork

theorem generationBlockEdge_succ (rule : Rule) (coarse fine : ℕ)
    (edge : Fin (rule.generation coarse).edges) (child : Fin (rule.generation fine).edges)
    (leaf : Fin rule.edges) :
    (rule.generationBlockDecomposition coarse (fine + 1)).edge.symm
        (finProdFinEquiv (edge, finProdFinEquiv (child, leaf))) =
      finProdFinEquiv
        ((rule.generationBlockDecomposition coarse fine).edge.symm (finProdFinEquiv (edge, child)), leaf) := by
  apply (rule.generationBlockDecomposition coarse (fine + 1)).edge.injective
  rw [Equiv.apply_symm_apply]
  change finProdFinEquiv (edge, finProdFinEquiv (child, leaf)) =
    substitutionAssociatorEdge (finProdFinEquiv
      (Prod.map (rule.generationBlockDecomposition coarse fine).edge id
        (finProdFinEquiv.symm (finProdFinEquiv
          ((rule.generationBlockDecomposition coarse fine).edge.symm (finProdFinEquiv (edge, child)), leaf)))))
  rw [Equiv.symm_apply_apply]
  change _ = substitutionAssociatorEdge (finProdFinEquiv
    ((rule.generationBlockDecomposition coarse fine).edge
      ((rule.generationBlockDecomposition coarse fine).edge.symm (finProdFinEquiv (edge, child))), leaf))
  rw [Equiv.apply_symm_apply, substitutionAssociatorEdge_apply]

theorem generationTopEdge_succ (rule : Rule) (depth : ℕ)
    (edge : Fin rule.edges) (child : Fin (rule.generation depth).edges) (leaf : Fin rule.edges) :
    (rule.generationTopDecomposition (depth + 1)).edge.symm
        (finProdFinEquiv (edge, finProdFinEquiv (child, leaf))) =
      finProdFinEquiv
        ((rule.generationTopDecomposition depth).edge.symm (finProdFinEquiv (edge, child)), leaf) := by
  apply (rule.generationTopDecomposition (depth + 1)).edge.injective
  rw [Equiv.apply_symm_apply]
  change finProdFinEquiv (edge, finProdFinEquiv (child, leaf)) =
    substitutionAssociatorEdge (finProdFinEquiv
      (Prod.map (rule.generationTopDecomposition depth).edge id
        (finProdFinEquiv.symm (finProdFinEquiv
          ((rule.generationTopDecomposition depth).edge.symm (finProdFinEquiv (edge, child)), leaf)))))
  rw [Equiv.symm_apply_apply]
  change _ = substitutionAssociatorEdge (finProdFinEquiv
    ((rule.generationTopDecomposition depth).edge
      ((rule.generationTopDecomposition depth).edge.symm (finProdFinEquiv (edge, child))), leaf))
  rw [Equiv.apply_symm_apply, substitutionAssociatorEdge_apply]

theorem generationEdgeAddress_bottom (rule : Rule) (depth : ℕ)
    (edge : Fin (rule.generation depth).edges) (leaf : Fin rule.edges) :
    generationEdgeAddress rule (depth + 1) (finProdFinEquiv (edge, leaf)) =
      generationEdgeAddress rule depth edge ++ [leaf] := by
  induction depth with
  | zero =>
    change [(finProdFinEquiv.symm (finProdFinEquiv (edge, leaf))).1,
      (finProdFinEquiv.symm (finProdFinEquiv (edge, leaf))).2] = [(edge : Fin rule.edges), leaf]
    rw [Equiv.symm_apply_apply]
  | succ depth inductionHypothesis =>
    let pair := finProdFinEquiv.symm ((rule.generationTopDecomposition depth).edge edge)
    have edge_identity : edge = (rule.generationTopDecomposition depth).edge.symm (finProdFinEquiv (pair.1, pair.2)) := by
      simp only [pair, Prod.eta, Equiv.apply_symm_apply, Equiv.symm_apply_apply]
    rw [edge_identity]
    have reassociation := generationTopEdge_succ rule depth pair.1 pair.2 leaf
    rw [← reassociation, generationEdgeAddress_top, inductionHypothesis, generationEdgeAddress_top]
    rfl

theorem generationEdgeAddress_block (rule : Rule) (coarse fine : ℕ)
    (edge : Fin (rule.generation coarse).edges) (child : Fin (rule.generation fine).edges) :
    generationEdgeAddress rule (coarse + fine + 1)
      ((rule.generationBlockDecomposition coarse fine).edge.symm (finProdFinEquiv (edge, child))) =
      generationEdgeAddress rule coarse edge ++ generationEdgeAddress rule fine child := by
  induction fine with
  | zero =>
    change generationEdgeAddress rule (coarse + 1) (finProdFinEquiv (edge, child)) = _
    exact generationEdgeAddress_bottom rule coarse edge child
  | succ fine inductionHypothesis =>
    obtain ⟨pair, equality⟩ := finProdFinEquiv.surjective child
    rcases pair with ⟨child, leaf⟩
    subst equality
    rw [generationBlockEdge_succ]
    change generationEdgeAddress rule ((coarse + fine + 1) + 1)
      (finProdFinEquiv ((rule.generationBlockDecomposition coarse fine).edge.symm (finProdFinEquiv (edge, child)), leaf)) = _
    rw [generationEdgeAddress_bottom, inductionHypothesis, generationEdgeAddress_bottom, List.append_assoc]

theorem markedGenerationConfiguration_top_apply (rule : Rule)
    (marks : (List (Fin rule.edges) × Bool) → Configuration rule.edges)
    (depth : ℕ) (address : List (Fin rule.edges)) (opened : Bool)
    (edge : Fin rule.edges) (child : Fin (rule.generation depth).edges) :
    markedGenerationConfiguration rule marks (depth + 1) address opened
      ((rule.generationTopDecomposition depth).edge.symm (finProdFinEquiv (edge, child))) =
        markedGenerationConfiguration rule marks depth (address ++ [edge]) (marks (address, opened) edge) child :=
  congrFun (congrFun (markedGenerationConfiguration_topCells rule marks depth address opened) edge) child

theorem markedGenerationConfiguration_bottom_apply (rule : Rule)
    (marks : (List (Fin rule.edges) × Bool) → Configuration rule.edges)
    (depth : ℕ) (address : List (Fin rule.edges)) (opened : Bool)
    (edge : Fin (rule.generation depth).edges) (leaf : Fin rule.edges) :
    markedGenerationConfiguration rule marks (depth + 1) address opened (finProdFinEquiv (edge, leaf)) =
      marks (address ++ generationEdgeAddress rule depth edge,
        markedGenerationConfiguration rule marks depth address opened edge) leaf := by
  induction depth generalizing address opened with
  | zero =>
    change markedGenerationConfiguration rule marks 1 address opened
      ((rule.generationTopDecomposition 0).edge.symm (finProdFinEquiv (edge, leaf))) = _
    rw [markedGenerationConfiguration_top_apply]
    rfl
  | succ depth inductionHypothesis =>
    let pair := finProdFinEquiv.symm ((rule.generationTopDecomposition depth).edge edge)
    have edge_identity : edge = (rule.generationTopDecomposition depth).edge.symm (finProdFinEquiv (pair.1, pair.2)) := by
      simp only [pair, Prod.eta, Equiv.apply_symm_apply, Equiv.symm_apply_apply]
    rw [edge_identity]
    have reassociation := generationTopEdge_succ rule depth pair.1 pair.2 leaf
    rw [← reassociation, markedGenerationConfiguration_top_apply, inductionHypothesis,
      generationEdgeAddress_top, markedGenerationConfiguration_top_apply]
    simp only [List.append_assoc, List.singleton_append]

/-- A block child is the raw configuration of precisely its common-tree
address, with the original coarse edge state. This is equality on each sample. -/
theorem generationBlockCells_marked (rule : Rule)
    (marks : (List (Fin rule.edges) × Bool) → Configuration rule.edges)
    (coarse fine : ℕ) (address : List (Fin rule.edges)) (opened : Bool)
    (edge : Fin (rule.generation coarse).edges) :
    generationBlockCells rule coarse fine
      (markedGenerationConfiguration rule marks (coarse + fine + 1) address opened) edge =
        markedGenerationConfiguration rule marks fine (address ++ generationEdgeAddress rule coarse edge)
          (markedGenerationConfiguration rule marks coarse address opened edge) := by
  induction fine with
  | zero =>
    funext leaf
    change markedGenerationConfiguration rule marks (coarse + 1) address opened (finProdFinEquiv (edge, leaf)) = _
    exact markedGenerationConfiguration_bottom_apply rule marks coarse address opened edge leaf
  | succ fine inductionHypothesis =>
    funext bond
    obtain ⟨pair, equality⟩ := finProdFinEquiv.surjective bond
    rcases pair with ⟨child, leaf⟩
    subst equality
    rw [generationBlockCells_succ_apply]
    change markedGenerationConfiguration rule marks ((coarse + fine + 1) + 1) address opened
      (finProdFinEquiv ((rule.generationBlockDecomposition coarse fine).edge.symm (finProdFinEquiv (edge, child)), leaf)) = _
    rw [markedGenerationConfiguration_bottom_apply, generationEdgeAddress_block,
      markedGenerationConfiguration_bottom_apply]
    have child_identity := congrFun inductionHypothesis child
    rw [generationBlockCells_apply] at child_identity
    rw [child_identity, List.append_assoc]

end
end IGSIII.Chemical.Substitution
