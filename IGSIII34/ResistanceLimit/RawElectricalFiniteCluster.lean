import IGSIII34.ResistanceLimit.ElectricalPersistence
import IGSIII34.ResistanceLimit.PairContinuity

set_option autoImplicit false
set_option maxHeartbeats 2000000
namespace IGSIII34.ResistanceLimit
noncomputable section
open Universality Universality.FiniteNetwork IGSIII34.Percolation
open IGSIII.Chemical.Substitution IGSIII.Geometry

/-- The original unit-resistance finite cluster, normalized by the natural
electrical multiplier. Its metric is distinct from the stationary metric. -/
def RawElectricalFiniteCluster (rule : Rule)
    (configuration : ∀ depth, Configuration (rule.generation depth).edges)
    (_growth : ℝ) (_growthPositive : 0 < _growth) (depth : ℕ) : Type :=
  RetainedSkeletonVertex (rule.generation depth).network (configuration depth)

instance rawElectricalFiniteClusterMetricSpace (rule : Rule)
    (configuration : ∀ depth, Configuration (rule.generation depth).edges)
    (growth : ℝ) (growthPositive : 0 < growth) (depth : ℕ) :
    MetricSpace (RawElectricalFiniteCluster rule configuration growth growthPositive depth) :=
  actualComponentResistanceMetric (rule.generation depth).network (configuration depth)
    (fun _ => (growth ^ (depth + 1))⁻¹) (fun _ => inv_pos.mpr (pow_pos growthPositive _))

instance rawElectricalFiniteClusterFinite (rule : Rule)
    (configuration : ∀ depth, Configuration (rule.generation depth).edges)
    (growth : ℝ) (growthPositive : 0 < growth) (depth : ℕ) :
    Finite (RawElectricalFiniteCluster rule configuration growth growthPositive depth) :=
  inferInstanceAs (Finite (RetainedSkeletonVertex (rule.generation depth).network (configuration depth)))

instance rawElectricalFiniteClusterNonempty (rule : Rule)
    (configuration : ∀ depth, Configuration (rule.generation depth).edges)
    (growth : ℝ) (growthPositive : 0 < growth) (depth : ℕ) :
    Nonempty (RawElectricalFiniteCluster rule configuration growth growthPositive depth) :=
  ⟨⟨(rule.generation depth).network.source, SimpleGraph.Reachable.refl _⟩⟩

theorem rawElectricalFiniteCluster_dist (rule : Rule)
    (configuration : ∀ depth, Configuration (rule.generation depth).edges)
    (growth : ℝ) (growthPositive : 0 < growth) (depth : ℕ)
    (first last : RawElectricalFiniteCluster rule configuration growth growthPositive depth) :
    dist first last = pairResistance (network (rule.generation depth).network (configuration depth))
      (fun _ => 1) first.val last.val / growth ^ (depth + 1) := by
  change pairResistance _ (fun _ => (growth ^ (depth + 1))⁻¹) _ _ = _
  have scaling := pairResistance_scale (network (rule.generation depth).network (configuration depth))
    (fun _ => 1) (fun _ => zero_le_one) (growth ^ (depth + 1))⁻¹
    (inv_nonneg.mpr (pow_pos growthPositive _).le) first.val last.val
  simpa only [mul_one, div_eq_mul_inv, mul_comm] using scaling

end
end IGSIII34.ResistanceLimit
