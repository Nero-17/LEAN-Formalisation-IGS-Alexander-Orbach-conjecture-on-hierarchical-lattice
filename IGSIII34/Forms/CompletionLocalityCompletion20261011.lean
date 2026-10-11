import IGSIII34.Forms.CompletionDomainCompletion20261011
import IGSIII34.ResistanceLimit.StrongLocality

/-! Strong locality on the metric completion follows from the actual finite
edge mesh. Distances of conductive endpoints are bounded by their resistance,
using a skeleton minimizer rather than postulating the endpoint estimate. -/
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1200000
namespace IGSIII34.Forms
noncomputable section
open IGSIII34.ResistanceLimit Filter
open scoped Topology

variable {Carrier : Type*} [MetricSpace Carrier]
variable {Edge : ℕ → Type*} [∀ depth, Fintype (Edge depth)]
variable (endpoint : ∀ depth, Edge depth → Carrier × Carrier)
variable (conductance : ∀ depth, Edge depth → ℝ)
variable (nonnegative : ∀ depth edge, 0 ≤ conductance depth edge)
variable (attained : ∀ first last : Carrier, first ≠ last →
  ∃ potential : energyDomain endpoint conductance nonnegative,
    potential.val first = 0 ∧ potential.val last = 1 ∧
    limitingEnergy endpoint conductance potential.val = (dist first last)⁻¹)

include attained in
theorem trace_endpoint_distance_le_inverse_conductance
    (depth : ℕ) (edge : Edge depth) (conductive : conductance depth edge ≠ 0) :
    dist (endpoint depth edge).1 (endpoint depth edge).2 ≤ (conductance depth edge)⁻¹ := by
  have conductancePositive : 0 < conductance depth edge :=
    lt_of_le_of_ne (nonnegative depth edge) (Ne.symm conductive)
  by_cases equal : (endpoint depth edge).1 = (endpoint depth edge).2
  · rw [equal, dist_self]
    exact (inv_pos.mpr conductancePositive).le
  have distancePositive : 0 < dist (endpoint depth edge).1 (endpoint depth edge).2 := dist_pos.mpr equal
  obtain ⟨potential, firstValue, lastValue, energy⟩ := attained _ _ equal
  have termBelow := Finset.single_le_sum
    (fun other _ => mul_nonneg (nonnegative depth other) (sq_nonneg (potential.val (endpoint depth other).1 -
      potential.val (endpoint depth other).2))) (Finset.mem_univ edge)
  change conductance depth edge * (potential.val (endpoint depth edge).1 - potential.val (endpoint depth edge).2)^2 ≤
    traceEnergy endpoint conductance depth potential.val at termBelow
  have below := termBelow.trans (traceEnergy_le_limitingEnergy endpoint conductance nonnegative potential.property depth)
  rw [firstValue, lastValue, energy] at below
  norm_num only [zero_sub, neg_one_sq, mul_one] at below
  have multiplied := mul_le_mul_of_nonneg_right below distancePositive.le
  rw [inv_mul_cancel₀ distancePositive.ne'] at multiplied
  rw [← one_div]
  apply (le_div_iff₀ conductancePositive).mpr
  simpa only [one_div, mul_comm] using multiplied

def completionTraceEndpoint (depth : ℕ) (edge : Edge depth) :
    UniformSpace.Completion Carrier × UniformSpace.Completion Carrier :=
  ((endpoint depth edge).1, (endpoint depth edge).2)

theorem completionTraceEnergy_eq (depth : ℕ) (potential : UniformSpace.Completion Carrier → ℝ) :
    traceEnergy (completionTraceEndpoint endpoint) conductance depth potential =
      traceEnergy endpoint conductance depth (fun point : Carrier => potential point) := rfl

theorem completionLimitingEnergy_eq (potential : UniformSpace.Completion Carrier → ℝ) :
    limitingEnergy (completionTraceEndpoint endpoint) conductance potential =
      limitingEnergy endpoint conductance (fun point : Carrier => potential point) := rfl

theorem completionLimitingPairing_eq (first second : UniformSpace.Completion Carrier → ℝ) :
    limitingPairing (completionTraceEndpoint endpoint) conductance first second =
      limitingPairing endpoint conductance (fun point : Carrier => first point)
        (fun point : Carrier => second point) := rfl

include attained in
theorem completionLimitingPairing_strongly_local
    (monotone : ∀ potential, Monotone (fun depth => traceEnergy endpoint conductance depth potential))
    (mesh : ℕ → ℝ) (meshZero : Tendsto mesh atTop (𝓝 0))
    (edgeMesh : ∀ depth edge, conductance depth edge ≠ 0 → (conductance depth edge)⁻¹ ≤ mesh depth)
    {first second : C(UniformSpace.Completion Carrier, ℝ)}
    (firstFinite : first ∈ completionEnergyDomain endpoint conductance nonnegative)
    (secondFinite : second ∈ completionEnergyDomain endpoint conductance nonnegative)
    (neighborhood : Set (UniformSpace.Completion Carrier)) (openNeighborhood : IsOpen neighborhood)
    (supportCompact : IsCompact (closure (Function.support (second : UniformSpace.Completion Carrier → ℝ))))
    (supportSubset : closure (Function.support (second : UniformSpace.Completion Carrier → ℝ)) ⊆ neighborhood)
    (constant : ∀ firstPoint ∈ neighborhood, ∀ secondPoint ∈ neighborhood,
      first firstPoint = first secondPoint) :
    limitingPairing endpoint conductance (fun point : Carrier => first point)
      (fun point : Carrier => second point) = 0 := by
  apply limitingPairing_strongly_local (completionTraceEndpoint endpoint) conductance nonnegative
    (fun potential => monotone (fun point : Carrier => potential point)) mesh meshZero
    (fun depth edge conductive => ?_) firstFinite secondFinite neighborhood openNeighborhood
    supportCompact supportSubset constant
  rw [completionTraceEndpoint, UniformSpace.Completion.dist_eq]
  exact (trace_endpoint_distance_le_inverse_conductance endpoint conductance nonnegative attained depth edge conductive).trans
    (edgeMesh depth edge conductive)

include attained in
theorem completionLimitingPairing_strongly_local_of_eventual_mesh
    (monotone : ∀ potential, Monotone (fun depth => traceEnergy endpoint conductance depth potential))
    (mesh : ℕ → ℝ) (meshZero : Tendsto mesh atTop (𝓝 0))
    (edgeMesh : ∀ᶠ depth in atTop, ∀ edge, conductance depth edge ≠ 0 →
      (conductance depth edge)⁻¹ ≤ mesh depth)
    {first second : C(UniformSpace.Completion Carrier, ℝ)}
    (firstFinite : first ∈ completionEnergyDomain endpoint conductance nonnegative)
    (secondFinite : second ∈ completionEnergyDomain endpoint conductance nonnegative)
    (neighborhood : Set (UniformSpace.Completion Carrier)) (openNeighborhood : IsOpen neighborhood)
    (supportCompact : IsCompact (closure (Function.support (second : UniformSpace.Completion Carrier → ℝ))))
    (supportSubset : closure (Function.support (second : UniformSpace.Completion Carrier → ℝ)) ⊆ neighborhood)
    (constant : ∀ firstPoint ∈ neighborhood, ∀ secondPoint ∈ neighborhood,
      first firstPoint = first secondPoint) :
    limitingPairing endpoint conductance (fun point : Carrier => first point)
      (fun point : Carrier => second point) = 0 := by
  obtain ⟨threshold, bounds⟩ := eventually_atTop.mp edgeMesh
  let modified : ℕ → ℝ := fun depth => if threshold ≤ depth then mesh depth else
    ∑ edge, |(conductance depth edge)⁻¹|
  have modifiedZero : Tendsto modified atTop (𝓝 0) := meshZero.congr'
    ((eventually_ge_atTop threshold).mono (fun depth after => by simp [modified, after]))
  apply completionLimitingPairing_strongly_local endpoint conductance nonnegative attained monotone
    modified modifiedZero ?_ firstFinite secondFinite neighborhood openNeighborhood supportCompact supportSubset constant
  intro depth edge conductive
  by_cases after : threshold ≤ depth
  · simpa only [modified, if_pos after] using bounds depth after edge conductive
  · dsimp only [modified]
    rw [if_neg after]
    exact (le_abs_self _).trans (Finset.single_le_sum
      (fun other _ => abs_nonneg ((conductance depth other)⁻¹)) (Finset.mem_univ edge))

end
end IGSIII34.Forms
