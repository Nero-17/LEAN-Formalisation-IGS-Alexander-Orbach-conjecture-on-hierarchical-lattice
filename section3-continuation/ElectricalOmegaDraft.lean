import IGSIII34.Percolation.ElectricalNormalization
import IGSIII34.Percolation.GrowthCompactResistance
import IGSIII.Probability.OmegaOrbit
import IGSIII.Probability.CompactScaling

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace IGSIII34.Percolation
noncomputable section
open Universality Universality.FiniteNetwork MeasureTheory
open IGSIII.Probability IGSIII.Chemical.Substitution
open scoped _root_.Topology ENNReal

noncomputable def electricalOrbitLp (rule : Rule) (p : ℝ) (positive : 0 < p)
    (belowOne : p < 1) (fixedPoint : rule.network.reliability p = p) (growth : ℝ) :
    ℕ → Lp ℝ 2 (independentInnovationLaw rule p positive belowOne fixedPoint) :=
  fun depth => (normalizedElectricalTransferLp rule p positive belowOne fixedPoint 2 growth)^[depth]
    (chemicalUnitLp rule p positive belowOne fixedPoint 2)

def electricalOmegaSet (rule : Rule) (p : ℝ) (positive : 0 < p)
    (belowOne : p < 1) (fixedPoint : rule.network.reliability p = p) (growth : ℝ) :
    Set (Lp ℝ 2 (independentInnovationLaw rule p positive belowOne fixedPoint)) :=
  orbitClusterSet (electricalOrbitLp rule p positive belowOne fixedPoint growth)

theorem electricalOrbitLp_successor (rule : Rule) (p : ℝ) (positive : 0 < p)
    (belowOne : p < 1) (fixedPoint : rule.network.reliability p = p) (growth : ℝ) (depth : ℕ) :
    electricalOrbitLp rule p positive belowOne fixedPoint growth (depth + 1) =
      normalizedElectricalTransferLp rule p positive belowOne fixedPoint 2 growth
        (electricalOrbitLp rule p positive belowOne fixedPoint growth depth) :=
  Function.iterate_succ_apply' _ _ _

theorem electricalOrbitLp_tail_eq_actual (rule : Rule) (classical : rule.Classical)
    (p : ℝ) (positive : 0 < p) (belowOne : p < 1)
    (fixedPoint : rule.network.reliability p = p) (growth : ℝ)
    (growthNonnegative : 0 ≤ growth) (depth : ℕ) :
    electricalOrbitLp rule p positive belowOne fixedPoint growth (depth + 1) =
      markedObservableLp rule p positive belowOne fixedPoint depth [] true
        (growthScaledResistance rule growth depth) := by
  apply Lp.ext
  filter_upwards [normalizedElectricalTransferLp_iterate_ae rule p positive belowOne fixedPoint
      2 growth growthNonnegative (depth+1),
    independentInnovationLaw_crosses rule p positive belowOne fixedPoint,
    markedObservableLp_ae rule p positive belowOne fixedPoint depth [] true
      (growthScaledResistance rule growth depth)] with marks iterateEquality crossing observableEquality
  change _ = _ at iterateEquality
  rw [electricalOrbitLp, iterateEquality, observableEquality,
    nonnegativeElectricalTransfer_iterate_actual]
  unfold growthScaledResistance
  rw [markedGeneration_resistance_eq_iteration rule marks crossing]
  simp only [inv_pow, div_eq_mul_inv]
  ring

theorem electricalOrbitLp_compact_closure (rule : Rule) (classical : rule.Classical)
    (p : ℝ) (positive : 0 < p) (belowOne : p < 1)
    (fixedPoint : rule.network.reliability p = p) (constant growth : ℝ)
    (growthPositive : 0 < growth)
    (growthBounds : ∀ depth, growth ^ depth ≤ (electricalOrbitScale rule p positive belowOne fixedPoint depth : ℝ) ∧
      (electricalOrbitScale rule p positive belowOne fixedPoint depth : ℝ) ≤ constant⁻¹ * growth ^ depth) :
    IsCompact (closure (Set.range (electricalOrbitLp rule p positive belowOne fixedPoint growth))) := by
  apply compact_closure_seed_and_tail _ (chemicalUnitLp rule p positive belowOne fixedPoint 2)
    (fun depth => markedObservableLp rule p positive belowOne fixedPoint depth [] true
      (growthScaledResistance rule growth depth))
    (markedGrowthScaledResistanceFamily_compact_closure rule classical p positive belowOne
      fixedPoint [] constant growth growthPositive growthBounds) rfl
  exact electricalOrbitLp_tail_eq_actual rule classical p positive belowOne fixedPoint growth growthPositive.le

theorem electricalOmegaSet_properties (rule : Rule) (classical : rule.Classical)
    (p : ℝ) (positive : 0 < p) (belowOne : p < 1)
    (fixedPoint : rule.network.reliability p = p) (constant growth : ℝ)
    (growthPositive : 0 < growth)
    (growthBounds : ∀ depth, growth ^ depth ≤ (electricalOrbitScale rule p positive belowOne fixedPoint depth : ℝ) ∧
      (electricalOrbitScale rule p positive belowOne fixedPoint depth : ℝ) ≤ constant⁻¹ * growth ^ depth) :
    (electricalOmegaSet rule p positive belowOne fixedPoint growth).Nonempty ∧
      IsCompact (electricalOmegaSet rule p positive belowOne fixedPoint growth) ∧
      Set.MapsTo (normalizedElectricalTransferLp rule p positive belowOne fixedPoint 2 growth)
        (electricalOmegaSet rule p positive belowOne fixedPoint growth)
        (electricalOmegaSet rule p positive belowOne fixedPoint growth) ∧
      Set.SurjOn (normalizedElectricalTransferLp rule p positive belowOne fixedPoint 2 growth)
        (electricalOmegaSet rule p positive belowOne fixedPoint growth)
        (electricalOmegaSet rule p positive belowOne fixedPoint growth) := by
  have precompact := electricalOrbitLp_compact_closure rule classical p positive belowOne fixedPoint
    constant growth growthPositive growthBounds
  have continuous := normalizedElectricalTransferLp_continuous rule p positive belowOne fixedPoint 2 growth
  have recursion := electricalOrbitLp_successor rule p positive belowOne fixedPoint growth
  exact ⟨orbitClusterSet_nonempty _ precompact, orbitClusterSet_compact _ precompact,
    orbitClusterSet_forward _ continuous _ recursion,
    orbitClusterSet_onto _ continuous _ recursion precompact⟩


end
end IGSIII34.Percolation
