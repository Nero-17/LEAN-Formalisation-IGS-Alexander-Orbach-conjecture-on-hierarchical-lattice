import IGSIII.Chemical.SubstitutionPaths.IndependentInnovations

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

/-!
# Exact finite laws of independent pairs of configuration innovations

The tree weight is the product of the actual crossing and noncrossing rule
weights at every address. Selection by a parent's edge state is performed
inside the graph construction. The resulting entire finite configuration,
and therefore its complete coarsening history, has the established IGS II law.
-/

namespace IGSIII.Chemical.Substitution

open Universality Universality.FiniteNetwork
open scoped BigOperators

@[reducible] def FiniteInnovationTree (rule : Rule) : ℕ → Type
  | 0 => Bool → Configuration rule.edges
  | depth + 1 => (Bool → Configuration rule.edges) × (Fin rule.edges → FiniteInnovationTree rule depth)

instance finiteInnovationTreeFintype (rule : Rule) : (depth : ℕ) → Fintype (FiniteInnovationTree rule depth)
  | 0 => inferInstanceAs (Fintype (Bool → Configuration rule.edges))
  | depth + 1 => by
      letI := finiteInnovationTreeFintype rule depth
      exact inferInstanceAs (Fintype ((Bool → Configuration rule.edges) ×
        (Fin rule.edges → FiniteInnovationTree rule depth)))

noncomputable def finiteInnovationWeight (rule : Rule) (p : ℝ) :
    (depth : ℕ) → FiniteInnovationTree rule depth → ℝ
  | 0, tree => ∏ opened, rule.network.conditionalCellWeight p opened (tree opened)
  | depth + 1, tree =>
      (∏ opened, rule.network.conditionalCellWeight p opened (tree.1 opened)) *
        ∏ edge, finiteInnovationWeight rule p depth (tree.2 edge)

noncomputable def finiteInnovationConfiguration (rule : Rule) :
    (depth : ℕ) → FiniteInnovationTree rule depth → Bool → Configuration (rule.generation depth).edges
  | 0, tree, opened => tree opened
  | depth + 1, tree, opened =>
      (generationTopCellsEquiv rule depth).symm
        (fun edge => finiteInnovationConfiguration rule depth (tree.2 edge) (tree.1 opened edge))

theorem finite_product_state_selection_observable
    {index source target : Type*} [Fintype index] [Fintype source] [Fintype target]
    [DecidableEq index] [DecidableEq target]
    (weight : index → source → ℝ) (transport : index → source → target)
    (pushedWeight : index → target → ℝ)
    (pushforward : ∀ edge output,
      pushedWeight edge output = ∑ sample, if transport edge sample = output then weight edge sample else 0)
    (response : (index → target) → ℝ) :
    (∑ output : index → target, (∏ edge, pushedWeight edge (output edge)) * response output) =
      ∑ sample : index → source, (∏ edge, weight edge (sample edge)) *
        response (fun edge => transport edge (sample edge)) := by
  classical
  simp_rw [pushforward, Fintype.prod_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro sample _
  rw [Finset.sum_eq_single (fun edge => transport edge (sample edge))]
  · simp
  · intro output _ different
    have mismatch : ∃ edge, transport edge (sample edge) ≠ output edge := by
      by_contra allMatch
      push Not at allMatch
      exact different (funext (fun edge => (allMatch edge).symm))
    obtain ⟨edge, mismatch⟩ := mismatch
    have zero : (∏ coordinate, if transport coordinate (sample coordinate) = output coordinate then
        weight coordinate (sample coordinate) else 0) = 0 :=
      Finset.prod_eq_zero (Finset.mem_univ edge) (if_neg mismatch)
    rw [zero, zero_mul]
  · simp

theorem rule_innovation_pair_observable (rule : Rule)
    (p : ℝ) (positive : 0 < p) (lessOne : p < 1)
    (fixedPoint : rule.network.reliability p = p) (opened : Bool)
    (response : Configuration rule.edges → ℝ) :
    (∑ pair : Bool → Configuration rule.edges,
      (∏ state, rule.network.conditionalCellWeight p state (pair state)) * response (pair opened)) =
      ∑ configuration, rule.network.conditionalCellWeight p opened configuration * response configuration := by
  rw [finite_product_local_moment]
  simp only [rule.network.sum_conditionalCellWeight p (by rwa [fixedPoint]) (by rwa [fixedPoint]),
    Finset.prod_const_one, one_mul]

/-- Every observable of the actual full generation has its conditioned
Bernoulli law under independent pairs, including the noncrossing cells. -/
theorem finite_innovation_configuration_observable (rule : Rule)
    (p : ℝ) (positive : 0 < p) (lessOne : p < 1)
    (fixedPoint : rule.network.reliability p = p) (depth : ℕ) (opened : Bool)
    (response : Configuration (rule.generation depth).edges → ℝ) :
    (∑ tree : FiniteInnovationTree rule depth,
      finiteInnovationWeight rule p depth tree * response (finiteInnovationConfiguration rule depth tree opened)) =
      ∑ configuration, (rule.generation depth).network.conditionalCellWeight p opened configuration *
        response configuration := by
  classical
  induction depth generalizing opened with
  | zero => exact rule_innovation_pair_observable rule p positive lessOne fixedPoint opened response
  | succ depth inductionHypothesis =>
      change (∑ tree : (Bool → Configuration rule.edges) × (Fin rule.edges → FiniteInnovationTree rule depth),
        ((∏ state, rule.network.conditionalCellWeight p state (tree.1 state)) *
          ∏ edge, finiteInnovationWeight rule p depth (tree.2 edge)) *
            response ((generationTopCellsEquiv rule depth).symm
              (fun edge => finiteInnovationConfiguration rule depth (tree.2 edge) (tree.1 opened edge)))) = _
      rw [Fintype.sum_prod_type]
      simp only [mul_assoc, ← Finset.mul_sum]
      have children (coarse : Configuration rule.edges) :
          (∑ subtrees : Fin rule.edges → FiniteInnovationTree rule depth,
            (∏ edge, finiteInnovationWeight rule p depth (subtrees edge)) *
              response ((generationTopCellsEquiv rule depth).symm
                (fun edge => finiteInnovationConfiguration rule depth (subtrees edge) (coarse edge)))) =
            ∑ cells : Fin rule.edges → Configuration (rule.generation depth).edges,
              (∏ edge, (rule.generation depth).network.conditionalCellWeight p (coarse edge) (cells edge)) *
                response ((generationTopCellsEquiv rule depth).symm cells) := by
        symm
        refine finite_product_state_selection_observable
          (fun _ subtree => finiteInnovationWeight rule p depth subtree)
          (fun edge subtree => finiteInnovationConfiguration rule depth subtree (coarse edge))
          (fun edge cell => (rule.generation depth).network.conditionalCellWeight p (coarse edge) cell)
          ?_ (fun cells => response ((generationTopCellsEquiv rule depth).symm cells))
        intro edge configuration
        have atom := inductionHypothesis (coarse edge)
          (fun selected => if selected = configuration then 1 else 0)
        simpa only [mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true] using atom.symm
      simp_rw [children]
      rw [rule_innovation_pair_observable rule p positive lessOne fixedPoint opened
        (fun coarse => ∑ cells : Fin rule.edges → Configuration (rule.generation depth).edges,
          (∏ edge, (rule.generation depth).network.conditionalCellWeight p (coarse edge) (cells edge)) *
            response ((generationTopCellsEquiv rule depth).symm cells))]
      have law := generation_root_children_observable rule p positive lessOne fixedPoint opened depth
        (fun _ cells => response ((generationTopCellsEquiv rule depth).symm cells))
      simpa only [generationTopCells, Equiv.symm_apply_apply] using law.symm

theorem finiteInnovationWeight_nonneg (rule : Rule) (p : ℝ) (nonnegative : 0 ≤ p)
    (atMostOne : p ≤ 1) (depth : ℕ) (tree : FiniteInnovationTree rule depth) :
    0 ≤ finiteInnovationWeight rule p depth tree := by
  induction depth with
  | zero => exact Finset.prod_nonneg (fun state _ =>
      rule.network.conditionalCellWeight_nonneg nonnegative atMostOne state (tree state))
  | succ depth inductionHypothesis =>
      exact mul_nonneg
        (Finset.prod_nonneg (fun state _ =>
          rule.network.conditionalCellWeight_nonneg nonnegative atMostOne state (tree.1 state)))
        (Finset.prod_nonneg (fun edge _ => inductionHypothesis (tree.2 edge)))

theorem finiteInnovationWeight_sum (rule : Rule)
    (p : ℝ) (positive : 0 < p) (lessOne : p < 1)
    (fixedPoint : rule.network.reliability p = p) (depth : ℕ) :
    ∑ tree : FiniteInnovationTree rule depth, finiteInnovationWeight rule p depth tree = 1 := by
  have law := finite_innovation_configuration_observable rule p positive lessOne fixedPoint depth true (fun _ => 1)
  simp only [mul_one] at law
  rw [law]
  exact (rule.generation depth).network.sum_conditionalCellWeight p
    (by rwa [rule.generation_fixed_point p fixedPoint])
    (by rwa [rule.generation_fixed_point p fixedPoint]) true

/-- Full finite-cylinder identification: all coarsened levels have the
existing joint history law, not just the terminal-distance marginal. -/
theorem finite_innovation_history_observable (rule : Rule)
    (p : ℝ) (positive : 0 < p) (lessOne : p < 1)
    (fixedPoint : rule.network.reliability p = p) (opened : Bool) (depth : ℕ)
    (response : rule.ConfigurationHistory depth → ℝ) :
    (∑ tree : FiniteInnovationTree rule depth,
      finiteInnovationWeight rule p depth tree *
        response (Rule.ConfigurationHistory.ofFine rule depth
          (finiteInnovationConfiguration rule depth tree opened))) =
      ∑ history : rule.ConfigurationHistory depth,
        Rule.ConfigurationHistory.recursiveWeight rule p opened depth history * response history := by
  rw [finite_innovation_configuration_observable rule p positive lessOne fixedPoint depth opened
    (fun configuration => response (Rule.ConfigurationHistory.ofFine rule depth configuration))]
  exact (Rule.ConfigurationHistory.joint_observable_law rule p positive lessOne fixedPoint opened depth response).symm

end IGSIII.Chemical.Substitution
