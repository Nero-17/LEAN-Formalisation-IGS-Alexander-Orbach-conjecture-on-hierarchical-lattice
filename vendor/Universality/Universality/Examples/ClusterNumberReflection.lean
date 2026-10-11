import Universality.Examples.ClusterNumberForcing
import Universality.Percolation.WheatstoneReliability
import Universality.Percolation.ClusterNumberSeries
import Universality.Percolation.ClusterNumberCriticalValue

namespace Universality
noncomputable section
open FiniteNetwork

def unitIntervalReflection (p : Set.Icc (0 : ℝ) 1) : Set.Icc (0 : ℝ) 1 :=
  ⟨1 - p.val, by constructor <;> linarith [p.property.1, p.property.2]⟩

theorem wheatstone_reliability_reflection (p : ℝ) :
    wheatstoneNetwork.reliability (1 - p) = 1 - wheatstoneNetwork.reliability p := by
  rw [wheatstone_reliability, wheatstone_reliability]
  ring

theorem wheatstone_forcing_reflection (p : ℝ) :
    2 * wheatstoneNetwork.expectedInternalClusterNumber p -
      2 * wheatstoneNetwork.expectedInternalClusterNumber (1 - p) =
      4 - 10 * p + 2 * wheatstoneNetwork.reliability p := by
  rw [wheatstone_expectedInternalClusterNumber, wheatstone_expectedInternalClusterNumber,
    wheatstone_reliability]
  ring

theorem wheatstone_unitReliability_reflection (p : Set.Icc (0 : ℝ) 1) :
    wheatstoneNetwork.unitReliability (unitIntervalReflection p) =
      unitIntervalReflection (wheatstoneNetwork.unitReliability p) := by
  apply Subtype.ext
  exact wheatstone_reliability_reflection p.val

theorem wheatstone_clusterNumberSeries_half :
    wheatstoneNetwork.clusterNumberSeries ⟨1 / 2, by norm_num⟩ = 9 / 64 := by
  rw [wheatstoneNetwork.clusterNumberSeries_fixed_point (by norm_num)
    _ (by rw [wheatstone_reliability]; norm_num), wheatstone_expectedInternalClusterNumber]
  norm_num

/-- Reflection symmetry for the actual volume-limit density, obtained from
the exact finite graph forcing polynomial and uniqueness of the bounded solution. -/
theorem wheatstone_clusterNumberSeries_reflection (p : Set.Icc (0 : ℝ) 1) :
    wheatstoneNetwork.clusterNumberSeries p -
      wheatstoneNetwork.clusterNumberSeries (unitIntervalReflection p) = 1 - 2 * p.val := by
  obtain ⟨bound, hbound⟩ := wheatstoneNetwork.clusterNumberSeries_bounded (by norm_num)
  have heq : (fun q : Set.Icc (0 : ℝ) 1 =>
      wheatstoneNetwork.clusterNumberSeries (unitIntervalReflection q) + 1 - 2 * q.val) =
      wheatstoneNetwork.clusterNumberSeries := by
    apply wheatstoneNetwork.clusterNumberSeries_unique (by norm_num) _ (bound + 3)
    · intro q
      obtain ⟨hlower, hupper⟩ := abs_le.mp (hbound (unitIntervalReflection q))
      apply abs_le.mpr
      constructor <;> linarith [q.property.1, q.property.2]
    · intro q
      have h := wheatstoneNetwork.clusterNumberSeries_equation (by norm_num)
        (unitIntervalReflection q)
      rw [wheatstone_unitReliability_reflection] at h
      have hforcing := wheatstone_forcing_reflection q.val
      norm_num at h ⊢
      change 5 * (wheatstoneNetwork.clusterNumberSeries (unitIntervalReflection q) +
        1 - 2 * q.val) -
        (wheatstoneNetwork.clusterNumberSeries
          (unitIntervalReflection (wheatstoneNetwork.unitReliability q)) +
          1 - 2 * wheatstoneNetwork.reliability q.val) = _
      change 5 * wheatstoneNetwork.clusterNumberSeries (unitIntervalReflection q) -
        wheatstoneNetwork.clusterNumberSeries
          (unitIntervalReflection (wheatstoneNetwork.unitReliability q)) =
        2 * wheatstoneNetwork.expectedInternalClusterNumber (1 - q.val) at h
      linarith
  have h := congrFun heq p
  linarith

end
end Universality
