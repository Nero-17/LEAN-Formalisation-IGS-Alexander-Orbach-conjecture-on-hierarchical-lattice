import IGSIII.Chemical.SubstitutionPaths.CompactChemicalFamily
import IGSIII.Chemical.SmallBall.FiniteDepthScaledMoments

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace IGSIII.Chemical.Substitution

open Universality Universality.FiniteNetwork MeasureTheory
open IGSIII.Probability IGSIII.Chemical.SmallBall
open scoped Topology ENNReal

theorem markedObservableLp_scale (rule : Rule)
    (p : ℝ) (positive : 0 < p) (lessOne : p < 1)
    (fixedPoint : rule.network.reliability p = p)
    (depth : ℕ) (address : List (Fin rule.edges)) (opened : Bool)
    (response : Configuration (rule.generation depth).edges → ℝ) (factor : ℝ) :
    markedObservableLp rule p positive lessOne fixedPoint depth address opened (fun configuration => factor * response configuration) =
      factor • markedObservableLp rule p positive lessOne fixedPoint depth address opened response := by
  apply Lp.ext
  filter_upwards [markedObservableLp_ae rule p positive lessOne fixedPoint depth address opened (fun configuration => factor * response configuration),
    markedObservableLp_ae rule p positive lessOne fixedPoint depth address opened response,
    Lp.coeFn_smul factor (markedObservableLp rule p positive lessOne fixedPoint depth address opened response)]
      with marks scaledEquality originalEquality scalarEquality
  simp only [scaledEquality, scalarEquality, Pi.smul_apply, smul_eq_mul, originalEquality]

noncomputable def markedGrowthScaledDistanceFamily (rule : Rule)
    (p : ℝ) (positive : 0 < p) (lessOne : p < 1)
    (fixedPoint : rule.network.reliability p = p) (address : List (Fin rule.edges)) (growth : ℝ) :
    Set (Lp ℝ 2 (independentInnovationLaw rule p positive lessOne fixedPoint)) :=
  Set.range (fun depth => markedObservableLp rule p positive lessOne fixedPoint depth address true
    (growthScaledDistance rule growth depth))

theorem markedGrowthScaledDistanceFamily_compact_closure
    (rule : Rule) (classical : rule.Classical)
    (p : ℝ) (positive : 0 < p) (lessOne : p < 1)
    (fixedPoint : rule.network.reliability p = p) (address : List (Fin rule.edges))
    (constant growth : ℝ) (growthPositive : 0 < growth)
    (growthBounds : ∀ depth, growth ^ depth ≤ manuscriptDistanceMean rule p depth ∧
      manuscriptDistanceMean rule p depth ≤ constant⁻¹ * growth ^ depth) :
    IsCompact (closure (markedGrowthScaledDistanceFamily rule p positive lessOne fixedPoint address growth)) := by
  have compactImage : IsCompact ((fun pair : ℝ × Lp ℝ 2 (independentInnovationLaw rule p positive lessOne fixedPoint) =>
      pair.1 • pair.2) '' (Set.Icc 1 constant⁻¹ ×ˢ
        closure (markedNormalizedDistanceFamily rule p positive lessOne fixedPoint address))) :=
    (isCompact_Icc.prod (markedNormalizedDistanceFamily_compact_closure rule classical p positive lessOne fixedPoint address)).image
      (continuous_fst.smul continuous_snd)
  apply compactImage.of_isClosed_subset isClosed_closure
  apply closure_minimal _ compactImage.isClosed
  rintro _ ⟨depth, rfl⟩
  have meanPositive : 0 < conditionedDistanceMean (rule.generation depth).network p :=
    lt_of_lt_of_le zero_lt_one (conditionedDistanceMean_atLeastOne _ positive.le lessOne.le
      (by rwa [rule.generation_fixed_point p fixedPoint])
      (by rwa [rule.generation_fixed_point p fixedPoint]))
  have lower : 1 ≤ conditionedDistanceMean (rule.generation depth).network p / growth ^ (depth + 1) := by
    apply (le_div_iff₀ (pow_pos growthPositive _)).mpr
    simpa only [one_mul, manuscriptDistanceMean] using (growthBounds (depth + 1)).1
  have upper : conditionedDistanceMean (rule.generation depth).network p / growth ^ (depth + 1) ≤ constant⁻¹ := by
    apply (div_le_iff₀ (pow_pos growthPositive _)).mpr
    exact (growthBounds (depth + 1)).2
  refine ⟨(conditionedDistanceMean (rule.generation depth).network p / growth ^ (depth + 1),
    markedObservableLp rule p positive lessOne fixedPoint depth address true
      (normalizedDistance (rule.generation depth).network p)),
    ⟨⟨lower, upper⟩, subset_closure ⟨depth, rfl⟩⟩, ?_⟩
  dsimp only
  rw [← markedObservableLp_scale]
  congr 1
  funext configuration
  exact (growthScaledDistance_eq_mean_ratio rule p growth growthPositive depth meanPositive configuration).symm

theorem exists_actual_chemical_growth_compact_family
    (rule : Rule) (classical : rule.Classical)
    (p : ℝ) (positive : 0 < p) (lessOne : p < 1)
    (fixedPoint : rule.network.reliability p = p) :
    ∃ constant growth : ℝ, 0 < constant ∧ constant ≤ 1 ∧
      (rule.network.fullGraph.dist rule.network.source rule.network.target : ℝ) ≤ growth ∧
      growth ≤ longestTerminalPath rule.network ∧
      (∀ depth, growth ^ depth ≤ manuscriptDistanceMean rule p depth ∧
        manuscriptDistanceMean rule p depth ≤ constant⁻¹ * growth ^ depth) ∧
      ∀ address : List (Fin rule.edges),
        IsCompact (closure (markedGrowthScaledDistanceFamily rule p positive lessOne fixedPoint address growth)) := by
  obtain ⟨constant, growth, constantPositive, constantAtMostOne, growthLower, growthUpper, growthBounds⟩ :=
    exists_actual_chemical_growth rule classical p positive lessOne fixedPoint
  refine ⟨constant, growth, constantPositive, constantAtMostOne, growthLower, growthUpper, growthBounds, fun address => ?_⟩
  apply markedGrowthScaledDistanceFamily_compact_closure rule classical p positive lessOne fixedPoint address constant growth _ growthBounds
  exact lt_of_lt_of_le (by exact_mod_cast Nat.zero_lt_of_lt classical.scale) growthLower

end IGSIII.Chemical.Substitution
