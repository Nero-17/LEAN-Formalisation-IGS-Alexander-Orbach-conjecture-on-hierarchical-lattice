import IGSIII4.SpectralDensity.ActualFamily20261012
import IGSIII4.SpectralDensity.ActualMomentPathPotential20261012
import IGSIII34.Resistance.SupportedCurrentPruningCompletion20261011
import Mathlib.Algebra.BigOperators.Fin

set_option autoImplicit false
set_option maxHeartbeats 0
set_option backward.isDefEq.respectTransparency false

namespace IGSIII4.SpectralDensity.ActualFamily
noncomputable section
open scoped BigOperators
open IGSIII34.Resistance
attribute [local instance] Classical.propDecidable

def fullElectricalNetwork (blocks paths interior : ℕ) :
    IGSIII34.Resistance.FiniteNetwork (Vertex blocks paths interior) (Edge blocks paths interior) where
  endpoint := endpoint blocks paths interior
  source := source blocks paths interior
  target := target blocks paths interior
  distinct := by simp [source, target]

def openElectricalNetwork (blocks paths interior : ℕ)
    (configuration : Edge blocks paths interior → Bool) :
    IGSIII34.Resistance.FiniteNetwork (Vertex blocks paths interior)
      {edge : Edge blocks paths interior // configuration edge = true} where
  endpoint edge := endpoint blocks paths interior edge.val
  source := source blocks paths interior
  target := target blocks paths interior
  distinct := by simp [source, target]

theorem sum_consecutive_difference20261012 {length : ℕ} (values : Fin (length + 1) → ℝ) :
    (∑ edge : Fin length, (values edge.castSucc - values edge.succ)) =
      values 0 - values (Fin.last length) := by
  have first := Fin.sum_univ_succ values
  have last := Fin.sum_univ_castSucc values
  rw [Finset.sum_sub_distrib]
  linarith

def circuitCurrent (blocks paths interior : ℕ) (shortCurrent exteriorCurrent : ℝ)
    (pathCurrent : Fin blocks → Fin paths → ℝ) : Edge blocks paths interior → ℝ
  | .inl edge => if edge.val < 2 then shortCurrent else exteriorCurrent
  | .inr (block, path, _) => pathCurrent block path

theorem path_divergence_sum20261012 {blocks paths interior : ℕ}
    (block : Fin blocks) (path : Fin paths) (vertex : Vertex blocks paths interior) :
    (∑ edge : Fin (interior + 2),
      ((if (pathVertex blocks paths interior block path edge.castSucc) = vertex then (1 : ℝ) else 0) -
       (if (pathVertex blocks paths interior block path edge.succ) = vertex then (1 : ℝ) else 0))) =
      (if Sum.inr (Sum.inl block.castSucc) = vertex then 1 else 0) -
      (if Sum.inr (Sum.inl block.succ) = vertex then 1 else 0) := by
  rw [sum_consecutive_difference20261012 (fun position =>
    if pathVertex blocks paths interior block path position = vertex then (1 : ℝ) else 0)]
  simp [pathVertex]

theorem circuitCurrent_divergence20261012 {blocks paths interior : ℕ}
    (shortCurrent exteriorCurrent : ℝ) (pathCurrent : Fin blocks → Fin paths → ℝ)
    (blockBalance : ∀ block, ∑ path, pathCurrent block path = exteriorCurrent)
    (vertex : Vertex blocks paths interior) :
    (fullElectricalNetwork blocks paths interior).divergence
      (circuitCurrent blocks paths interior shortCurrent exteriorCurrent pathCurrent) vertex =
        (shortCurrent + exteriorCurrent) *
          ((if source blocks paths interior = vertex then 1 else 0) -
           (if target blocks paths interior = vertex then 1 else 0)) := by
  have pathSum (block : Fin blocks) (path : Fin paths) :
      (∑ edge : Fin (interior + 2), pathCurrent block path *
        ((if (pathVertex blocks paths interior block path edge.castSucc) = vertex then (1 : ℝ) else 0) -
         (if (pathVertex blocks paths interior block path edge.succ) = vertex then (1 : ℝ) else 0))) =
        pathCurrent block path *
          ((if Sum.inr (Sum.inl block.castSucc) = vertex then 1 else 0) -
           (if Sum.inr (Sum.inl block.succ) = vertex then 1 else 0)) := by
    rw [← Finset.mul_sum, path_divergence_sum20261012]
  have blockSum (block : Fin blocks) :
      (∑ path, pathCurrent block path *
          ((if Sum.inr (Sum.inl block.castSucc) = vertex then (1 : ℝ) else 0) -
           (if Sum.inr (Sum.inl block.succ) = vertex then 1 else 0))) =
        exteriorCurrent *
          ((if Sum.inr (Sum.inl block.castSucc) = vertex then 1 else 0) -
           (if Sum.inr (Sum.inl block.succ) = vertex then 1 else 0)) := by
    rw [← Finset.sum_mul, blockBalance]
  have chainSum : (∑ block : Fin blocks,
      ((if (Sum.inr (Sum.inl block.castSucc) : Vertex blocks paths interior) = vertex then (1 : ℝ) else 0) -
       (if Sum.inr (Sum.inl block.succ) = vertex then (1 : ℝ) else 0))) =
      (if Sum.inr (Sum.inl (0 : Fin (blocks + 1))) = vertex then 1 else 0) -
      (if Sum.inr (Sum.inl (Fin.last blocks)) = vertex then 1 else 0) :=
    sum_consecutive_difference20261012
      (fun junction => if (Sum.inr (Sum.inl junction) : Vertex blocks paths interior) = vertex then 1 else 0)
  change (∑ edge, circuitCurrent blocks paths interior shortCurrent exteriorCurrent pathCurrent edge *
    ((if (endpoint blocks paths interior edge).1 = vertex then (1 : ℝ) else 0) -
      (if (endpoint blocks paths interior edge).2 = vertex then 1 else 0))) = _
  simp only [Fintype.sum_sum_type, Fintype.sum_prod_type, circuitCurrent, endpoint]
  simp only [pathSum, blockSum]
  rw [← Finset.mul_sum, chainSum]
  simp only [Fin.sum_univ_succ, Fin.val_zero, Fin.val_succ]
  norm_num
  ring

theorem circuitCurrent_unit_flow20261012 {blocks paths interior : ℕ}
    (shortCurrent exteriorCurrent : ℝ) (pathCurrent : Fin blocks → Fin paths → ℝ)
    (blockBalance : ∀ block, ∑ path, pathCurrent block path = exteriorCurrent)
    (total : shortCurrent + exteriorCurrent = 1) :
    circuitCurrent blocks paths interior shortCurrent exteriorCurrent pathCurrent ∈
      (fullElectricalNetwork blocks paths interior).unitFlows := by
  intro vertex
  rw [circuitCurrent_divergence20261012 shortCurrent exteriorCurrent pathCurrent blockBalance, total, one_mul]
  change ((if source blocks paths interior = vertex then (1 : ℝ) else 0) -
    (if target blocks paths interior = vertex then 1 else 0)) =
      ((if vertex = source blocks paths interior then (1 : ℝ) else 0) -
    (if vertex = target blocks paths interior then 1 else 0))
  simp only [eq_comm]

end
end IGSIII4.SpectralDensity.ActualFamily
