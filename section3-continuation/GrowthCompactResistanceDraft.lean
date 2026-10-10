import IGSIII34.Percolation.CompactResistanceFamily
import IGSIII.Chemical.SubstitutionPaths.GrowthCompactFamily

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace IGSIII34.Percolation
noncomputable section
open Universality Universality.FiniteNetwork MeasureTheory
open IGSIII.Probability IGSIII.Chemical.Substitution
open scoped _root_.Topology ENNReal

def growthScaledResistance (rule : Rule) (growth : ℝ) (depth : ℕ)
    (configuration : Configuration (rule.generation depth).edges) : ℝ :=
  unitConfigurationResistance (rule.generation depth).network configuration / growth^(depth+1)

noncomputable def markedGrowthScaledResistanceFamily (rule : Rule)
    (p : ℝ) (positive : 0 < p) (lessOne : p < 1)
    (fixedPoint : rule.network.reliability p = p) (address : List (Fin rule.edges)) (growth : ℝ) :
    Set (Lp ℝ 2 (independentInnovationLaw rule p positive lessOne fixedPoint)) :=
  Set.range (fun depth => markedObservableLp rule p positive lessOne fixedPoint depth address true
    (growthScaledResistance rule growth depth))

theorem markedGrowthScaledResistanceFamily_compact_closure
    (rule : Rule) (classical : rule.Classical)
    (p : ℝ) (positive : 0 < p) (lessOne : p < 1)
    (fixedPoint : rule.network.reliability p = p) (address : List (Fin rule.edges))
    (constant growth : ℝ) (growthPositive : 0 < growth)
    (growthBounds : ∀ depth, growth ^ depth ≤ (electricalOrbitScale rule p positive lessOne fixedPoint depth : ℝ) ∧
      (electricalOrbitScale rule p positive lessOne fixedPoint depth : ℝ) ≤ constant⁻¹ * growth ^ depth) :
    IsCompact (closure (markedGrowthScaledResistanceFamily rule p positive lessOne fixedPoint address growth)) := by
  have compactImage : IsCompact ((fun pair : ℝ × Lp ℝ 2 (independentInnovationLaw rule p positive lessOne fixedPoint) =>
      pair.1 • pair.2) '' (Set.Icc 1 constant⁻¹ ×ˢ
        closure (markedNormalizedResistanceFamily rule p positive lessOne fixedPoint address))) :=
    (isCompact_Icc.prod (markedNormalizedResistanceFamily_compact_closure rule classical p positive lessOne fixedPoint address)).image
      (continuous_fst.smul continuous_snd)
  apply compactImage.of_isClosed_subset isClosed_closure
  apply closure_minimal _ compactImage.isClosed
  rintro _ ⟨depth, rfl⟩
  have meanPositive := generation_conditionalMeanResistance_positive rule classical p positive lessOne fixedPoint depth
  have lower : 1 ≤ conditionalMeanResistance (rule.generation depth).network p / growth ^ (depth + 1) := by
    apply (le_div_iff₀ (pow_pos growthPositive _)).mpr
    have bound := (growthBounds (depth+1)).1
    simpa only [one_mul, electricalOrbitScale_succ_eq_generation_mean rule classical p positive lessOne fixedPoint] using bound
  have upper : conditionalMeanResistance (rule.generation depth).network p / growth ^ (depth + 1) ≤ constant⁻¹ := by
    apply (div_le_iff₀ (pow_pos growthPositive _)).mpr
    have bound := (growthBounds (depth+1)).2
    simpa only [electricalOrbitScale_succ_eq_generation_mean rule classical p positive lessOne fixedPoint] using bound
  refine ⟨(conditionalMeanResistance (rule.generation depth).network p / growth ^ (depth + 1),
    markedObservableLp rule p positive lessOne fixedPoint depth address true
      (normalizedConfigurationResistance (rule.generation depth).network p)),
    ⟨⟨lower, upper⟩, subset_closure ⟨depth, rfl⟩⟩, ?_⟩
  dsimp only
  rw [← markedObservableLp_scale]
  congr 1
  funext configuration
  unfold growthScaledResistance normalizedConfigurationResistance
  field_simp


end
end IGSIII34.Percolation
