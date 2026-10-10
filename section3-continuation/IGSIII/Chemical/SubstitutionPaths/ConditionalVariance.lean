import IGSIII.Chemical.SubstitutionPaths.ConnectedProductLaw
import Universality.Graph.GeodesicEdgeLevels

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 0

/-!
# Actual coarse-conditioned chemical variance

The left-hand side below is the variance under the established conditional
product of the actual fine cell configurations, averaged over the actual
coarse connected law. Connected-product transport identifies the same
quantity with independent connected child distances. Efron--Stein and the
inverse-moment geodesic estimate then give a bound in actual finite-distance
moments; no conditional variance estimate is assumed.
-/

namespace IGSIII.Chemical.Substitution

open Universality Universality.FiniteNetwork
open IGSIII.Probability IGSIII.Chemical.SmallBall
open scoped BigOperators

theorem actual_substitution_connected_distance_observable
    {outerVertices outerEdges innerVertices innerEdges : ℕ}
    (outer : FiniteNetwork outerVertices outerEdges) (inner : FiniteNetwork innerVertices innerEdges)
    (simple : Function.Injective (fun edge => s((outer.endpoint edge).1, (outer.endpoint edge).2)))
    (p : ℝ) (positive : 0 < p) (lessOne : p < 1)
    (innerFixedPoint : inner.reliability p = p)
    (response : ℝ → ℝ) :
    finiteMean ((outer.substitute inner).conditionalCellWeight p true)
      (fun configuration => response
        (((outer.substitute inner).openGraph configuration).dist
          (outer.substitute inner).source (outer.substitute inner).target /
            conditionedDistanceMean inner p)) =
      finiteMean (outer.conditionalCellWeight p true) (fun coarse =>
        finiteMean (tupleWeight (fun _ : Fin outerEdges => inner.conditionalCellWeight p true))
          (fun cells => response ((edgePathFamily outer coarse).shortest
            (fun edge => positiveNormalizedDistance inner p (cells edge))))) := by
  have meanPositive : 0 < conditionedDistanceMean inner p :=
    lt_of_lt_of_le zero_lt_one (conditionedDistanceMean_atLeastOne inner positive.le lessOne.le
      (by rwa [innerFixedPoint]) (by rwa [innerFixedPoint]))
  have law := conditional_substitution_distance_observable outer inner simple p
    (by rwa [innerFixedPoint]) (by rwa [innerFixedPoint])
    (fun distance => response (distance / conditionedDistanceMean inner p))
  rw [innerFixedPoint] at law
  change _ = finiteMean (outer.conditionalCellWeight p true) (fun coarse =>
    finiteMean (tupleWeight (fun edge => inner.conditionalCellWeight p (coarse edge)))
      (fun cells => response (cellMinPlus outer inner coarse cells / conditionedDistanceMean inner p))) at law
  refine law.trans ?_
  unfold finiteMean
  apply Finset.sum_congr rfl
  intro coarse _
  congr 1
  exact actual_cellMinPlus_connected_product outer inner simple p
    (by rwa [innerFixedPoint]) (by rwa [innerFixedPoint]) meanPositive coarse response

theorem actual_substitution_conditional_variance_bound
    {outerVertices outerEdges innerVertices innerEdges : ℕ}
    (outer : FiniteNetwork outerVertices outerEdges) (inner : FiniteNetwork innerVertices innerEdges)
    (simple : Function.Injective (fun edge => s((outer.endpoint edge).1, (outer.endpoint edge).2)))
    (p : ℝ) (positive : 0 < p) (lessOne : p < 1)
    (outerFixedPoint : outer.reliability p = p) (innerFixedPoint : inner.reliability p = p)
    {power : ℝ} (powerAtLeastTwo : 2 ≤ power)
    (secondMoment inverseMoment : ℝ) (secondMomentNonnegative : 0 ≤ secondMoment)
    (inverseMomentNonnegative : 0 ≤ inverseMoment)
    (secondMomentBound : normalizedDistanceMoment inner p 2 ≤ secondMoment)
    (inverseMomentBound : finiteMean (inner.conditionalCellWeight p true)
      (fun configuration => (normalizedDistance inner p configuration)⁻¹ ^ power) ≤ inverseMoment) :
    finiteMean (outer.conditionalCellWeight p true) (fun coarse =>
      finiteVariance (tupleWeight (fun edge => inner.conditionalCellWeight p (coarse edge)))
        (fun cells => cellMinPlus outer inner coarse cells / conditionedDistanceMean inner p)) ≤
      2 * secondMoment *
        (finiteMean ((outer.substitute inner).conditionalCellWeight p true)
          (fun configuration =>
            (((outer.substitute inner).openGraph configuration).dist
              (outer.substitute inner).source (outer.substitute inner).target /
                conditionedDistanceMean inner p) ^ 2)) ^ (1 / (2 : ℝ)) *
                  ((outerEdges : ℝ) * inverseMoment) ^ (1 / power) := by
  have meanPositive : 0 < conditionedDistanceMean inner p :=
    lt_of_lt_of_le zero_lt_one (conditionedDistanceMean_atLeastOne inner positive.le lessOne.le
      (by rwa [innerFixedPoint]) (by rwa [innerFixedPoint]))
  have varianceEquality := fun coarse => actual_cellMinPlus_connected_variance outer inner simple p
    (by rwa [innerFixedPoint]) (by rwa [innerFixedPoint]) meanPositive coarse
  simp_rw [varianceEquality]
  have bound := shortest_mixture_variance_le_product_moments
    (outer.conditionalCellWeight p true) (edgePathFamily outer)
    (fun (_ : Configuration outerEdges) (_ : Fin outerEdges) => inner.conditionalCellWeight p true)
    (fun (_ : Configuration outerEdges) (_ : Fin outerEdges) => positiveNormalizedDistance inner p)
    powerAtLeastTwo
    (fun coarse => outer.conditionalCellWeight_nonneg positive.le lessOne.le true coarse)
    (outer.sum_conditionalCellWeight p (by rwa [outerFixedPoint]) (by rwa [outerFixedPoint]) true)
    (fun _ _ configuration => inner.conditionalCellWeight_nonneg positive.le lessOne.le true configuration)
    (fun _ _ => inner.sum_conditionalCellWeight p (by rwa [innerFixedPoint]) (by rwa [innerFixedPoint]) true)
    (fun _ _ configuration => positiveNormalizedDistance_positive inner p meanPositive configuration)
    secondMoment inverseMoment secondMomentNonnegative inverseMomentNonnegative
    (fun _ _ => by
      rw [positiveNormalizedDistance_observable inner p (fun value => value ^ 2)]
      exact secondMomentBound)
    (fun _ _ => by
      rw [positiveNormalizedDistance_observable inner p (fun value => value⁻¹ ^ power)]
      exact inverseMomentBound)
  have secondLaw := actual_substitution_connected_distance_observable outer inner simple p positive lessOne
    innerFixedPoint (fun value => value ^ 2)
  calc
    _ ≤ 2 * secondMoment *
        (finiteMean (outer.conditionalCellWeight p true) (fun coarse =>
          finiteMean (tupleWeight (fun _ : Fin outerEdges => inner.conditionalCellWeight p true))
            (fun cells => ((edgePathFamily outer coarse).shortest
              (fun edge => positiveNormalizedDistance inner p (cells edge))) ^ 2))) ^ (1 / (2 : ℝ)) *
                ((outerEdges : ℝ) * inverseMoment) ^ (1 / power) := bound
    _ = _ := by rw [← secondLaw]

noncomputable def generationBlockCellsEquiv (rule : Rule) (coarse fine : ℕ) :
    Configuration (rule.generation (coarse + fine + 1)).edges ≃
      (Fin (rule.generation coarse).edges → Configuration (rule.generation fine).edges) :=
  (rule.generationBlockDecomposition coarse fine).configuration.trans substitutionConfigurationEquiv.symm

noncomputable def generationBlockCells (rule : Rule) (coarse fine : ℕ)
    (configuration : Configuration (rule.generation (coarse + fine + 1)).edges) :
    Fin (rule.generation coarse).edges → Configuration (rule.generation fine).edges :=
  generationBlockCellsEquiv rule coarse fine configuration

noncomputable def generationBlockCoarse (rule : Rule) (coarse fine : ℕ)
    (configuration : Configuration (rule.generation (coarse + fine + 1)).edges) :
    Configuration (rule.generation coarse).edges :=
  (rule.generation fine).network.coarseConfiguration (generationBlockCells rule coarse fine configuration)

theorem actual_generation_block_observable (rule : Rule)
    (p : ℝ) (positive : 0 < p) (lessOne : p < 1)
    (fixedPoint : rule.network.reliability p = p) (coarse fine : ℕ)
    (response : Configuration (rule.generation coarse).edges →
      (Fin (rule.generation coarse).edges → Configuration (rule.generation fine).edges) → ℝ) :
    (∑ configuration : Configuration (rule.generation (coarse + fine + 1)).edges,
      (rule.generation (coarse + fine + 1)).network.conditionalCellWeight p true configuration *
        response (generationBlockCoarse rule coarse fine configuration)
          (generationBlockCells rule coarse fine configuration)) =
      ∑ outerConfiguration : Configuration (rule.generation coarse).edges,
        (rule.generation coarse).network.conditionalCellWeight p true outerConfiguration *
          ∑ cells : Fin (rule.generation coarse).edges → Configuration (rule.generation fine).edges,
            (∏ edge, (rule.generation fine).network.conditionalCellWeight p (outerConfiguration edge) (cells edge)) *
              response outerConfiguration cells := by
  have law := (rule.generation coarse).network.conditional_substitution_observable
    (rule.generation fine).network p
    (by rwa [rule.generation_fixed_point p fixedPoint])
    (by rwa [rule.generation_fixed_point p fixedPoint]) true response
  rw [← (generationBlockCellsEquiv rule coarse fine).sum_comp] at law
  change (∑ configuration,
    ((rule.generation coarse).network.substitute (rule.generation fine).network).conditionalCellWeight p true
      (substitutionConfigurationEquiv (generationBlockCells rule coarse fine configuration)) *
        response (generationBlockCoarse rule coarse fine configuration)
          (generationBlockCells rule coarse fine configuration)) = _ at law
  have configurationIdentity (configuration : Configuration (rule.generation (coarse + fine + 1)).edges) :
      substitutionConfigurationEquiv (generationBlockCells rule coarse fine configuration) =
        (rule.generationBlockDecomposition coarse fine).configuration configuration := by
    simp [generationBlockCells, generationBlockCellsEquiv]
  simp_rw [configurationIdentity, NetworkEquivalence.conditionalCellWeight,
    rule.generation_fixed_point p fixedPoint] at law
  exact law

end IGSIII.Chemical.Substitution
