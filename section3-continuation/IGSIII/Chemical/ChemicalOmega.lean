import IGSIII.Chemical.TransferNormalization
import IGSIII.Chemical.SubstitutionPaths.GrowthCompactFamily
import IGSIII.Probability.OmegaOrbit
import IGSIII.Probability.CompactScaling

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace IGSIII.Chemical.Substitution

open Universality Universality.FiniteNetwork MeasureTheory
open IGSIII.Probability IGSIII.Chemical.SmallBall
open scoped Topology ENNReal

noncomputable def chemicalOrbit (rule : Rule) (p : ℝ) (positive : 0 < p)
    (belowOne : p < 1) (fixedPoint : rule.network.reliability p = p) (growth : ℝ) :
    ℕ → Lp ℝ 2 (independentInnovationLaw rule p positive belowOne fixedPoint) :=
  fun depth => (normalizedChemicalTransferLp rule p positive belowOne fixedPoint 2 growth)^[depth]
    (chemicalUnitLp rule p positive belowOne fixedPoint 2)

def chemicalOmegaSet (rule : Rule) (p : ℝ) (positive : 0 < p)
    (belowOne : p < 1) (fixedPoint : rule.network.reliability p = p) (growth : ℝ) :
    Set (Lp ℝ 2 (independentInnovationLaw rule p positive belowOne fixedPoint)) :=
  orbitClusterSet (chemicalOrbit rule p positive belowOne fixedPoint growth)

theorem chemicalOrbit_successor (rule : Rule) (p : ℝ) (positive : 0 < p)
    (belowOne : p < 1) (fixedPoint : rule.network.reliability p = p) (growth : ℝ) (depth : ℕ) :
    chemicalOrbit rule p positive belowOne fixedPoint growth (depth + 1) =
      normalizedChemicalTransferLp rule p positive belowOne fixedPoint 2 growth
        (chemicalOrbit rule p positive belowOne fixedPoint growth depth) :=
  Function.iterate_succ_apply' _ _ _

theorem chemicalOrbit_tail_eq_actual (rule : Rule) (classical : rule.Classical)
    (p : ℝ) (positive : 0 < p) (belowOne : p < 1)
    (fixedPoint : rule.network.reliability p = p) (growth : ℝ)
    (growthNonnegative : 0 ≤ growth) (depth : ℕ) :
    chemicalOrbit rule p positive belowOne fixedPoint growth (depth + 1) =
      markedObservableLp rule p positive belowOne fixedPoint depth [] true
        (growthScaledDistance rule growth depth) := by
  apply Lp.ext
  filter_upwards [normalizedChemicalTransferLp_iterate_ae rule p positive belowOne fixedPoint
      2 growth growthNonnegative (depth + 1),
    chemicalTransfer_iterate_eq_actual_ae rule classical.simple p positive belowOne fixedPoint,
    markedObservableLp_ae rule p positive belowOne fixedPoint depth [] true
      (growthScaledDistance rule growth depth)] with marks iterateEquality actualEquality observableEquality
  change _ = _ at iterateEquality
  rw [chemicalOrbit, iterateEquality, observableEquality]
  have rootShift : innovationTreeShift rule [] marks = marks := by
    funext coordinate
    rfl
  have actualRoot := actualEquality depth []
  rw [rootShift] at actualRoot
  rw [actualRoot]
  simp only [growthScaledDistance, inv_pow, div_eq_mul_inv]
  ring

theorem chemicalOrbit_compact_closure (rule : Rule) (classical : rule.Classical)
    (p : ℝ) (positive : 0 < p) (belowOne : p < 1)
    (fixedPoint : rule.network.reliability p = p) (constant growth : ℝ)
    (growthPositive : 0 < growth)
    (growthBounds : ∀ depth, growth ^ depth ≤ manuscriptDistanceMean rule p depth ∧
      manuscriptDistanceMean rule p depth ≤ constant⁻¹ * growth ^ depth) :
    IsCompact (closure (Set.range (chemicalOrbit rule p positive belowOne fixedPoint growth))) := by
  apply compact_closure_seed_and_tail _ (chemicalUnitLp rule p positive belowOne fixedPoint 2)
    (fun depth => markedObservableLp rule p positive belowOne fixedPoint depth [] true
      (growthScaledDistance rule growth depth))
    (markedGrowthScaledDistanceFamily_compact_closure rule classical p positive belowOne
      fixedPoint [] constant growth growthPositive growthBounds) rfl
  exact chemicalOrbit_tail_eq_actual rule classical p positive belowOne fixedPoint growth growthPositive.le

theorem chemicalOmegaSet_properties (rule : Rule) (classical : rule.Classical)
    (p : ℝ) (positive : 0 < p) (belowOne : p < 1)
    (fixedPoint : rule.network.reliability p = p) (constant growth : ℝ)
    (growthPositive : 0 < growth)
    (growthBounds : ∀ depth, growth ^ depth ≤ manuscriptDistanceMean rule p depth ∧
      manuscriptDistanceMean rule p depth ≤ constant⁻¹ * growth ^ depth) :
    (chemicalOmegaSet rule p positive belowOne fixedPoint growth).Nonempty ∧
      IsCompact (chemicalOmegaSet rule p positive belowOne fixedPoint growth) ∧
      Set.MapsTo (normalizedChemicalTransferLp rule p positive belowOne fixedPoint 2 growth)
        (chemicalOmegaSet rule p positive belowOne fixedPoint growth)
        (chemicalOmegaSet rule p positive belowOne fixedPoint growth) ∧
      Set.SurjOn (normalizedChemicalTransferLp rule p positive belowOne fixedPoint 2 growth)
        (chemicalOmegaSet rule p positive belowOne fixedPoint growth)
        (chemicalOmegaSet rule p positive belowOne fixedPoint growth) := by
  have precompact := chemicalOrbit_compact_closure rule classical p positive belowOne fixedPoint
    constant growth growthPositive growthBounds
  have continuous := normalizedChemicalTransferLp_continuous rule p positive belowOne fixedPoint 2 growth
  have recursion := chemicalOrbit_successor rule p positive belowOne fixedPoint growth
  exact ⟨orbitClusterSet_nonempty _ precompact, orbitClusterSet_compact _ precompact,
    orbitClusterSet_forward _ continuous _ recursion,
    orbitClusterSet_onto _ continuous _ recursion precompact⟩

theorem exists_actual_chemical_omega (rule : Rule) (classical : rule.Classical)
    (p : ℝ) (positive : 0 < p) (belowOne : p < 1)
    (fixedPoint : rule.network.reliability p = p) :
    ∃ constant growth : ℝ, 0 < constant ∧ constant ≤ 1 ∧
      (rule.network.fullGraph.dist rule.network.source rule.network.target : ℝ) ≤ growth ∧
      growth ≤ longestTerminalPath rule.network ∧
      (∀ depth, growth ^ depth ≤ manuscriptDistanceMean rule p depth ∧
        manuscriptDistanceMean rule p depth ≤ constant⁻¹ * growth ^ depth) ∧
      (chemicalOmegaSet rule p positive belowOne fixedPoint growth).Nonempty ∧
      IsCompact (chemicalOmegaSet rule p positive belowOne fixedPoint growth) ∧
      Set.MapsTo (normalizedChemicalTransferLp rule p positive belowOne fixedPoint 2 growth)
        (chemicalOmegaSet rule p positive belowOne fixedPoint growth)
        (chemicalOmegaSet rule p positive belowOne fixedPoint growth) ∧
      Set.SurjOn (normalizedChemicalTransferLp rule p positive belowOne fixedPoint 2 growth)
        (chemicalOmegaSet rule p positive belowOne fixedPoint growth)
        (chemicalOmegaSet rule p positive belowOne fixedPoint growth) := by
  obtain ⟨constant, growth, constantPositive, constantAtMostOne, growthLower, growthUpper, growthBounds⟩ :=
    exists_actual_chemical_growth rule classical p positive belowOne fixedPoint
  have growthPositive : 0 < growth :=
    lt_of_lt_of_le (by exact_mod_cast Nat.zero_lt_of_lt classical.scale) growthLower
  exact ⟨constant, growth, constantPositive, constantAtMostOne, growthLower, growthUpper, growthBounds,
    chemicalOmegaSet_properties rule classical p positive belowOne fixedPoint constant growth growthPositive growthBounds⟩

end IGSIII.Chemical.Substitution
