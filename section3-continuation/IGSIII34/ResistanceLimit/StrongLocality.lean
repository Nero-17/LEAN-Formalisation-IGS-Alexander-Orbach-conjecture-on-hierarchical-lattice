import IGSIII34.ResistanceLimit.LimitEnergy
import Mathlib.Topology.MetricSpace.Thickening

/-!
# Strong locality from shrinking finite trace edges

The proof is independent of the electrical mesh estimate: it uses the topology
of the carrier and a vanishing mesh for trace-edge endpoints. Applying it to the
actual IGS carrier requires the finite trace system and its compatibility.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace IGSIII34.ResistanceLimit
noncomputable section
open Filter
open scoped Topology

variable {Carrier : Type*} [MetricSpace Carrier]
variable {Edge : ℕ → Type*} [∀ depth, Fintype (Edge depth)]
variable (endpoint : ∀ depth, Edge depth → Carrier × Carrier)
variable (conductance : ∀ depth, Edge depth → ℝ)

theorem tracePairing_eventually_zero_of_shrinking_mesh
    (mesh : ℕ → ℝ) (meshZero : Tendsto mesh atTop (𝓝 0))
    (edgeBound : ∀ depth edge, conductance depth edge ≠ 0 →
      dist (endpoint depth edge).1 (endpoint depth edge).2 ≤ mesh depth)
    (first second : Carrier → ℝ) (neighborhood : Set Carrier)
    (openNeighborhood : IsOpen neighborhood)
    (supportCompact : IsCompact (closure (Function.support second)))
    (supportSubset : closure (Function.support second) ⊆ neighborhood)
    (constant : ∀ firstPoint ∈ neighborhood, ∀ secondPoint ∈ neighborhood,
      first firstPoint = first secondPoint) :
    ∀ᶠ depth in atTop, tracePairing endpoint conductance depth first second = 0 := by
  obtain ⟨radius, radiusPositive, radiusSubset⟩ :=
    supportCompact.exists_thickening_subset_open openNeighborhood supportSubset
  have smallMesh : ∀ᶠ depth in atTop, mesh depth < radius :=
    (tendsto_order.mp meshZero).2 radius radiusPositive
  filter_upwards [smallMesh] with depth small
  apply finitePairing_eq_zero_of_edgewise
  intro edge
  by_cases zero : conductance depth edge = 0
  · exact Or.inl zero
  · right
    by_cases equal : second (endpoint depth edge).1 = second (endpoint depth edge).2
    · exact Or.inr equal
    · left
      have endpointClose : dist (endpoint depth edge).1 (endpoint depth edge).2 < radius :=
        (edgeBound depth edge zero).trans_lt small
      by_cases firstZero : second (endpoint depth edge).1 = 0
      · have lastNonzero : second (endpoint depth edge).2 ≠ 0 := by
          intro lastZero
          exact equal (firstZero.trans lastZero.symm)
        have lastSupport : (endpoint depth edge).2 ∈ closure (Function.support second) :=
          subset_closure lastNonzero
        have firstNeighborhood : (endpoint depth edge).1 ∈ neighborhood :=
          radiusSubset (Metric.mem_thickening_iff.mpr ⟨_, lastSupport, endpointClose⟩)
        exact constant _ firstNeighborhood _ (supportSubset lastSupport)
      · have firstSupport : (endpoint depth edge).1 ∈ closure (Function.support second) :=
          subset_closure firstZero
        have lastNeighborhood : (endpoint depth edge).2 ∈ neighborhood :=
          radiusSubset (Metric.mem_thickening_iff.mpr ⟨_, firstSupport, by rwa [dist_comm]⟩)
        exact constant _ (supportSubset firstSupport) _ lastNeighborhood

theorem limitingPairing_strongly_local
    (nonnegative : ∀ depth edge, 0 ≤ conductance depth edge)
    (monotone : ∀ potential, Monotone (fun depth => traceEnergy endpoint conductance depth potential))
    (mesh : ℕ → ℝ) (meshZero : Tendsto mesh atTop (𝓝 0))
    (edgeBound : ∀ depth edge, conductance depth edge ≠ 0 →
      dist (endpoint depth edge).1 (endpoint depth edge).2 ≤ mesh depth)
    {first second : Carrier → ℝ}
    (firstFinite : first ∈ energyDomain endpoint conductance nonnegative)
    (secondFinite : second ∈ energyDomain endpoint conductance nonnegative)
    (neighborhood : Set Carrier) (openNeighborhood : IsOpen neighborhood)
    (supportCompact : IsCompact (closure (Function.support second)))
    (supportSubset : closure (Function.support second) ⊆ neighborhood)
    (constant : ∀ firstPoint ∈ neighborhood, ∀ secondPoint ∈ neighborhood,
      first firstPoint = first secondPoint) :
    limitingPairing endpoint conductance first second = 0 :=
  limitingPairing_eq_zero_of_eventually endpoint conductance nonnegative monotone firstFinite secondFinite
    (tracePairing_eventually_zero_of_shrinking_mesh endpoint conductance mesh meshZero edgeBound
      first second neighborhood openNeighborhood supportCompact supportSubset constant)

theorem limitingPairing_strongly_local_compact [CompactSpace Carrier]
    (nonnegative : ∀ depth edge, 0 ≤ conductance depth edge)
    (monotone : ∀ potential, Monotone (fun depth => traceEnergy endpoint conductance depth potential))
    (mesh : ℕ → ℝ) (meshZero : Tendsto mesh atTop (𝓝 0))
    (edgeBound : ∀ depth edge, conductance depth edge ≠ 0 →
      dist (endpoint depth edge).1 (endpoint depth edge).2 ≤ mesh depth)
    {first second : Carrier → ℝ}
    (firstFinite : first ∈ energyDomain endpoint conductance nonnegative)
    (secondFinite : second ∈ energyDomain endpoint conductance nonnegative)
    (neighborhood : Set Carrier) (openNeighborhood : IsOpen neighborhood)
    (supportSubset : closure (Function.support second) ⊆ neighborhood)
    (constant : ∀ firstPoint ∈ neighborhood, ∀ secondPoint ∈ neighborhood,
      first firstPoint = first secondPoint) :
    limitingPairing endpoint conductance first second = 0 :=
  limitingPairing_strongly_local endpoint conductance nonnegative monotone mesh meshZero edgeBound
    firstFinite secondFinite neighborhood openNeighborhood isClosed_closure.isCompact supportSubset constant

end
end IGSIII34.ResistanceLimit
