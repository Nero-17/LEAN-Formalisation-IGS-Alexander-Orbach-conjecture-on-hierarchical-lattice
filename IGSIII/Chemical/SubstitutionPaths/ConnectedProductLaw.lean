import IGSIII.Chemical.SubstitutionPaths.RetentionLaw
import IGSIII.Chemical.SmallBall.FiniteDepthMoments
import IGSIII.Chemical.GeodesicMixtureEstimate

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 0

/-!
# Genuine connected-child product law for chemical observables

Only open coarse edges can occur in an actual terminal path. Consequently
closed coarse coordinates can be replaced by independent connected children
when evaluating any function of the chemical shortest path. The replacement
is proved by finite product transport. A positive completion on zero-weight
disconnected outcomes permits direct use of finite Efron--Stein estimates.
-/

namespace IGSIII.Chemical.Substitution

open Universality Universality.FiniteNetwork
open IGSIII.Probability IGSIII.Chemical.SmallBall
open scoped BigOperators

theorem finite_product_replace_unused {Outcome : Type*} [Fintype Outcome] [DecidableEq Outcome]
    {count : ℕ} (firstWeight secondWeight : Fin count → Outcome → ℝ)
    (firstNormalized : ∀ edge, ∑ outcome, firstWeight edge outcome = 1)
    (secondNormalized : ∀ edge, ∑ outcome, secondWeight edge outcome = 1)
    (active : Fin count → Bool) (default : Outcome)
    (same : ∀ edge, active edge = true → firstWeight edge = secondWeight edge)
    (response : (Fin count → Outcome) → ℝ)
    (usesActive : ∀ first second, (∀ edge, active edge = true → first edge = second edge) →
      response first = response second) :
    finiteMean (tupleWeight firstWeight) response = finiteMean (tupleWeight secondWeight) response := by
  classical
  let masked := fun (edge : Fin count) (outcome : Outcome) => if active edge then outcome else default
  let pushed := fun (edge : Fin count) (output : Outcome) =>
    ∑ outcome, if masked edge outcome = output then firstWeight edge outcome else 0
  have equalFiber (edge : Fin count) (output : Outcome) :
      pushed edge output = ∑ outcome, if masked edge outcome = output then secondWeight edge outcome else 0 := by
    cases opened : active edge with
    | true => simp only [pushed, same edge opened]
    | false =>
        by_cases atDefault : default = output
        · simp [pushed, masked, opened, atDefault, firstNormalized, secondNormalized]
        · simp [pushed, masked, opened, atDefault]
  have firstLaw := finite_product_state_selection_observable firstWeight masked pushed (fun _ _ => rfl) response
  have secondLaw := finite_product_state_selection_observable secondWeight masked pushed equalFiber response
  have maskedResponse (sample : Fin count → Outcome) :
      response (fun edge => masked edge (sample edge)) = response sample :=
    usesActive _ _ (fun edge opened => by simp [masked, opened])
  simpa only [maskedResponse, finiteMean, tupleWeight] using firstLaw.symm.trans secondLaw

theorem edgePathFamily_shortest_depends_open {vertices edges : ℕ}
    (network : FiniteNetwork vertices edges)
    (simple : Function.Injective (fun edge => s((network.endpoint edge).1, (network.endpoint edge).2)))
    (configuration : Configuration edges) (first second : Fin edges → ℝ)
    (same : ∀ edge, configuration edge = true → first edge = second edge) :
    (edgePathFamily network configuration).shortest first =
      (edgePathFamily network configuration).shortest second := by
  apply shortest_congr_used
  intro path membership edge used
  exact same edge (edgePathFamily_used_edge network simple configuration membership used)

noncomputable def positiveNormalizedDistance {vertices edges : ℕ}
    (network : FiniteNetwork vertices edges) (p : ℝ) (configuration : Configuration edges) : ℝ :=
  if network.crosses configuration then normalizedDistance network p configuration else 1

theorem positiveNormalizedDistance_positive {vertices edges : ℕ}
    (network : FiniteNetwork vertices edges) (p : ℝ)
    (meanPositive : 0 < conditionedDistanceMean network p) (configuration : Configuration edges) :
    0 < positiveNormalizedDistance network p configuration := by
  by_cases crossing : network.crosses configuration = true
  · simp only [positiveNormalizedDistance, crossing, ↓reduceIte, normalizedDistance]
    apply div_pos _ meanPositive
    exact_mod_cast ((network.crosses_eq_true _).mp crossing).pos_dist_of_ne network.terminals_distinct
  · simp [positiveNormalizedDistance, crossing]

theorem positiveNormalizedDistance_observable {vertices edges : ℕ}
    (network : FiniteNetwork vertices edges) (p : ℝ) (response : ℝ → ℝ) :
    finiteMean (network.conditionalCellWeight p true)
      (fun configuration => response (positiveNormalizedDistance network p configuration)) =
      finiteMean (network.conditionalCellWeight p true)
        (fun configuration => response (normalizedDistance network p configuration)) := by
  unfold finiteMean
  apply Finset.sum_congr rfl
  intro configuration _
  by_cases crossing : network.crosses configuration = true
  · simp [positiveNormalizedDistance, crossing]
  · simp [FiniteNetwork.conditionalCellWeight, crossing]

theorem actual_child_shortest_connected_product
    {outerVertices outerEdges innerVertices innerEdges : ℕ}
    (outer : FiniteNetwork outerVertices outerEdges) (inner : FiniteNetwork innerVertices innerEdges)
    (simple : Function.Injective (fun edge => s((outer.endpoint edge).1, (outer.endpoint edge).2)))
    (p : ℝ) (positive : 0 < inner.reliability p) (lessOne : inner.reliability p < 1)
    (coarse : Configuration outerEdges) (response : ℝ → ℝ) :
    finiteMean (tupleWeight (fun edge => inner.conditionalCellWeight p (coarse edge)))
      (fun cells => response ((edgePathFamily outer coarse).shortest
        (fun edge => normalizedDistance inner p (cells edge)))) =
      finiteMean (tupleWeight (fun _ : Fin outerEdges => inner.conditionalCellWeight p true))
        (fun cells => response ((edgePathFamily outer coarse).shortest
          (fun edge => positiveNormalizedDistance inner p (cells edge)))) := by
  classical
  calc
    _ = finiteMean (tupleWeight (fun edge => inner.conditionalCellWeight p (coarse edge)))
        (fun cells => response ((edgePathFamily outer coarse).shortest
          (fun edge => positiveNormalizedDistance inner p (cells edge)))) := by
      unfold finiteMean
      apply Finset.sum_congr rfl
      intro cells _
      by_cases zero : tupleWeight (fun edge => inner.conditionalCellWeight p (coarse edge)) cells = 0
      · simp [zero]
      · have shortestEquality : (edgePathFamily outer coarse).shortest
            (fun edge => normalizedDistance inner p (cells edge)) =
            (edgePathFamily outer coarse).shortest
              (fun edge => positiveNormalizedDistance inner p (cells edge)) := by
          apply edgePathFamily_shortest_depends_open outer simple coarse
          intro edge opened
          have crossing : inner.crosses (cells edge) = true := by
            by_contra disconnected
            apply zero
            change (∏ edge, inner.conditionalCellWeight p (coarse edge) (cells edge)) = 0
            apply Finset.prod_eq_zero (Finset.mem_univ edge)
            simp [opened, FiniteNetwork.conditionalCellWeight, disconnected]
          simp [positiveNormalizedDistance, crossing]
        exact congrArg (fun value => tupleWeight
          (fun edge => inner.conditionalCellWeight p (coarse edge)) cells * response value) shortestEquality
    _ = _ := finite_product_replace_unused (Outcome := Configuration innerEdges) (count := outerEdges)
      (fun edge => inner.conditionalCellWeight p (coarse edge))
      (fun _ : Fin outerEdges => inner.conditionalCellWeight p true)
      (fun edge => inner.sum_conditionalCellWeight p positive lessOne (coarse edge))
      (fun _ => inner.sum_conditionalCellWeight p positive lessOne true) coarse (fun _ => false)
      (fun edge opened => by rw [opened]) _ (by
        intro first second same
        apply congrArg response
        exact edgePathFamily_shortest_depends_open outer simple coarse _ _
          (fun edge opened => congrArg (positiveNormalizedDistance inner p) (same edge opened)))

theorem actual_cellMinPlus_connected_product
    {outerVertices outerEdges innerVertices innerEdges : ℕ}
    (outer : FiniteNetwork outerVertices outerEdges) (inner : FiniteNetwork innerVertices innerEdges)
    (simple : Function.Injective (fun edge => s((outer.endpoint edge).1, (outer.endpoint edge).2)))
    (p : ℝ) (positive : 0 < inner.reliability p) (lessOne : inner.reliability p < 1)
    (meanPositive : 0 < conditionedDistanceMean inner p)
    (coarse : Configuration outerEdges) (response : ℝ → ℝ) :
    finiteMean (tupleWeight (fun edge => inner.conditionalCellWeight p (coarse edge)))
      (fun cells => response (cellMinPlus outer inner coarse cells / conditionedDistanceMean inner p)) =
      finiteMean (tupleWeight (fun _ : Fin outerEdges => inner.conditionalCellWeight p true))
        (fun cells => response ((edgePathFamily outer coarse).shortest
          (fun edge => positiveNormalizedDistance inner p (cells edge)))) := by
  simp_rw [← cellMinPlus_normalizedDistance outer inner simple p meanPositive]
  exact actual_child_shortest_connected_product outer inner simple p positive lessOne coarse response

theorem actual_cellMinPlus_connected_variance
    {outerVertices outerEdges innerVertices innerEdges : ℕ}
    (outer : FiniteNetwork outerVertices outerEdges) (inner : FiniteNetwork innerVertices innerEdges)
    (simple : Function.Injective (fun edge => s((outer.endpoint edge).1, (outer.endpoint edge).2)))
    (p : ℝ) (positive : 0 < inner.reliability p) (lessOne : inner.reliability p < 1)
    (meanPositive : 0 < conditionedDistanceMean inner p) (coarse : Configuration outerEdges) :
    finiteVariance (tupleWeight (fun edge => inner.conditionalCellWeight p (coarse edge)))
      (fun cells => cellMinPlus outer inner coarse cells / conditionedDistanceMean inner p) =
      finiteVariance (tupleWeight (fun _ : Fin outerEdges => inner.conditionalCellWeight p true))
        (fun cells => (edgePathFamily outer coarse).shortest
          (fun edge => positiveNormalizedDistance inner p (cells edge))) := by
  rw [finiteVariance_eq_second_moment _ _ (tupleWeight_normalized _
    (fun edge => inner.sum_conditionalCellWeight p positive lessOne (coarse edge)))]
  rw [finiteVariance_eq_second_moment _ _ (tupleWeight_normalized _
    (fun _ => inner.sum_conditionalCellWeight p positive lessOne true))]
  rw [actual_cellMinPlus_connected_product outer inner simple p positive lessOne meanPositive coarse (fun value => value ^ 2)]
  have means := actual_cellMinPlus_connected_product outer inner simple p positive lessOne meanPositive coarse id
  simp only [id_eq] at means
  rw [means]

end IGSIII.Chemical.Substitution
