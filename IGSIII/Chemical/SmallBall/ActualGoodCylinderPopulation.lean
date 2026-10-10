import IGSIII.Chemical.SmallBall.GoodCylinderBorelCantelli
import IGSIII.Chemical.SmallBall.PositiveFieldGoodEvent
import IGSIII.Mass.MarkedConnectedPopulation

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000

namespace IGSIII.Chemical.SmallBall

open Universality Universality.FiniteNetwork MeasureTheory Substitution Filter Set Matrix IGSIII.Probability
open scoped BigOperators ENNReal Topology

noncomputable section

noncomputable def goodConnectedCylinderIndices (rule : Rule)
    (good : Set ((List (Fin rule.edges) × Bool) → Configuration rule.edges))
    (depth : ℕ) (marks : (List (Fin rule.edges) × Bool) → Configuration rule.edges) :
    Finset (Fin (rule.generation depth).edges) := by
  classical
  exact (connectedCylinderIndices (rule.generation depth).network (markedGenerationConfiguration rule marks depth [] true)).filter
    (fun edge => innovationTreeShift rule (generationEdgeAddress rule depth edge) marks ∈ good)

theorem goodConnectedCylinderIndices_card (rule : Rule)
    (good : Set ((List (Fin rule.edges) × Bool) → Configuration rule.edges))
    (depth : ℕ) (marks : (List (Fin rule.edges) × Bool) → Configuration rule.edges) :
    ((goodConnectedCylinderIndices rule good depth marks).card : ℝ) = goodConnectedCylinderCount rule good depth marks := by
  classical
  simp only [goodConnectedCylinderIndices, goodConnectedCylinderCount, Finset.card_filter,
    Nat.cast_sum, Nat.cast_ite, Nat.cast_one, Nat.cast_zero, Set.indicator_apply]

theorem goodConnectedCylinderIndices_mem (rule : Rule)
    (good : Set ((List (Fin rule.edges) × Bool) → Configuration rule.edges))
    (depth : ℕ) (marks : (List (Fin rule.edges) × Bool) → Configuration rule.edges)
    (edge : Fin (rule.generation depth).edges) :
    edge ∈ goodConnectedCylinderIndices rule good depth marks ↔
      (rule.generation depth).network.childState .connected (markedGenerationConfiguration rule marks depth [] true) edge = some .connected ∧
      innovationTreeShift rule (generationEdgeAddress rule depth edge) marks ∈ good := by
  classical
  simp only [goodConnectedCylinderIndices, connectedCylinderIndices, Finset.mem_filter, Finset.mem_univ, true_and]

theorem actual_good_connected_cylinder_population_lower
    (rule : Rule) (classicalRule : rule.Classical)
    (p : ℝ) (positive : 0 < p) (lessOne : p < 1) (fixedPoint : rule.network.reliability p = p)
    (good : Set ((List (Fin rule.edges) × Bool) → Configuration rule.edges))
    (goodMeasurable : MeasurableSet good)
    (goodPositive : 0 < (independentInnovationLaw rule p positive lessOne fixedPoint).real good) :
    ∀ᵐ marks ∂independentInnovationLaw rule p positive lessOne fixedPoint,
      ∃ coefficient : ℝ, 0 < coefficient ∧ ∀ᶠ depth : ℕ in atTop,
        coefficient * ((spectralRadius ℂ ((rule.network.massMatrix p).map Complex.ofReal)).toReal) ^ depth ≤
          ((goodConnectedCylinderIndices rule good depth marks).card : ℝ) := by
  have growthLarge : 1 < (spectralRadius ℂ ((rule.network.massMatrix p).map Complex.ofReal)).toReal :=
    (rule.network.interior_fixed_point_strictly_unstable p positive lessOne fixedPoint classicalRule.scale).trans
      (rule.interior_fixed_point_spectral_dominance p positive lessOne fixedPoint classicalRule.massAdmissible.symmetric classicalRule.scale).2.1
  have lower := ae_good_count_grows_of_positive_population
    (independentInnovationLaw rule p positive lessOne fixedPoint)
    (fun depth marks => ((rule.generation depth).network.liveCount .connected .connected
      (markedGenerationConfiguration rule marks depth [] true) : ℝ))
    (goodConnectedCylinderCount rule good)
    ((spectralRadius ℂ ((rule.network.massMatrix p).map Complex.ofReal)).toReal)
    ((independentInnovationLaw rule p positive lessOne fixedPoint).real good) growthLarge goodPositive
    (marked_connected_population_positive_limit classicalRule p positive lessOne fixedPoint)
    (actual_connected_good_count_lower_tail rule p positive lessOne fixedPoint good goodMeasurable)
  simpa only [goodConnectedCylinderIndices_card] using lower

theorem exists_positive_field_good_cylinder_population
    (rule : Rule) (classicalRule : rule.Classical)
    (p : ℝ) (positive : 0 < p) (lessOne : p < 1) (fixedPoint : rule.network.reliability p = p)
    (value : ((List (Fin rule.edges) × Bool) → Configuration rule.edges) → ℝ)
    (valueMeasurable : Measurable value)
    (valuePositive : ∀ᵐ marks ∂independentInnovationLaw rule p positive lessOne fixedPoint, 0 < value marks) :
    ∃ threshold : ℝ, 0 < threshold ∧
      ∀ᵐ marks ∂independentInnovationLaw rule p positive lessOne fixedPoint,
        ∃ coefficient : ℝ, 0 < coefficient ∧ ∀ᶠ depth : ℕ in atTop,
          coefficient * ((spectralRadius ℂ ((rule.network.massMatrix p).map Complex.ofReal)).toReal) ^ depth ≤
            ((goodConnectedCylinderIndices rule (positiveFieldGoodEvent rule value threshold) depth marks).card : ℝ) := by
  obtain ⟨threshold, thresholdPositive, goodPositive⟩ := exists_positive_field_good_event rule p positive lessOne fixedPoint value valuePositive
  exact ⟨threshold, thresholdPositive, actual_good_connected_cylinder_population_lower rule classicalRule p positive lessOne fixedPoint
    (positiveFieldGoodEvent rule value threshold) (positiveFieldGoodEvent_measurable rule value valueMeasurable threshold) goodPositive⟩

end
end IGSIII.Chemical.SmallBall