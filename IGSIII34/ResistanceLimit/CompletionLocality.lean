import IGSIII34.ResistanceLimit.StrongLocality
import IGSIII34.Forms.CompletionExtension

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
namespace IGSIII34.ResistanceLimit
noncomputable section
open IGSIII34.Forms Filter
open scoped Topology

variable {Carrier : Type*} [MetricSpace Carrier]
variable {Edge : ℕ → Type*} [∀ depth, Fintype (Edge depth)]
variable (endpoint : ∀ depth, Edge depth → Carrier × Carrier)
variable (conductance : ∀ depth, Edge depth → ℝ)
variable (nonnegative : ∀ depth edge, 0 ≤ conductance depth edge)
variable (monotone : ∀ potential, Monotone (fun depth => traceEnergy endpoint conductance depth potential))
variable (resistanceBound : ∀ potential ∈ energyDomain endpoint conductance nonnegative,
  ∀ first last, (potential first - potential last) ^ 2 ≤ dist first last * limitingEnergy endpoint conductance potential)

def completionEnergyEndpoint (depth : ℕ) (edge : Edge depth) :
    UniformSpace.Completion Carrier × UniformSpace.Completion Carrier :=
  ((endpoint depth edge).1, (endpoint depth edge).2)

theorem completion_traceEnergy (depth : ℕ) (potential : UniformSpace.Completion Carrier → ℝ) :
    traceEnergy (completionEnergyEndpoint endpoint) conductance depth potential =
      traceEnergy endpoint conductance depth (fun point => potential point) := by
  unfold traceEnergy finiteEnergy completionEnergyEndpoint
  rfl

include monotone in
theorem completion_traceEnergy_monotone (potential : UniformSpace.Completion Carrier → ℝ) :
    Monotone (fun depth => traceEnergy (completionEnergyEndpoint endpoint) conductance depth potential) := by
  simp only [completion_traceEnergy]
  exact monotone _

include resistanceBound in
theorem completionExtension_traceEnergy (potential : energyDomain endpoint conductance nonnegative) (depth : ℕ) :
    traceEnergy (completionEnergyEndpoint endpoint) conductance depth
      (completionExtension endpoint conductance nonnegative potential) =
      traceEnergy endpoint conductance depth potential.val := by
  rw [completion_traceEnergy]
  congr 1
  funext point
  exact completionExtension_coe endpoint conductance nonnegative resistanceBound potential point

include resistanceBound in
theorem completionExtension_energyDomain (potential : energyDomain endpoint conductance nonnegative) :
    (completionExtension endpoint conductance nonnegative potential : UniformSpace.Completion Carrier → ℝ) ∈
      energyDomain (completionEnergyEndpoint endpoint) conductance nonnegative := by
  obtain ⟨upper, upperBound⟩ := potential.property
  refine ⟨upper, ?_⟩
  rintro value ⟨depth, rfl⟩
  exact (completionExtension_traceEnergy endpoint conductance nonnegative resistanceBound potential depth).le.trans
    (upperBound (Set.mem_range_self depth))

include resistanceBound in
theorem completionExtension_limitingEnergy (potential : energyDomain endpoint conductance nonnegative) :
    limitingEnergy (completionEnergyEndpoint endpoint) conductance
      (completionExtension endpoint conductance nonnegative potential) =
      limitingEnergy endpoint conductance potential.val := by
  unfold limitingEnergy
  simp only [completionExtension_traceEnergy endpoint conductance nonnegative resistanceBound]

include resistanceBound in
theorem completionExtension_limitingPairing (first second : energyDomain endpoint conductance nonnegative) :
    limitingPairing (completionEnergyEndpoint endpoint) conductance
      (completionExtension endpoint conductance nonnegative first)
      (completionExtension endpoint conductance nonnegative second) =
      limitingPairing endpoint conductance first.val second.val := by
  unfold limitingPairing
  have sumIdentity : (fun point : UniformSpace.Completion Carrier =>
      completionExtension endpoint conductance nonnegative first point +
        completionExtension endpoint conductance nonnegative second point) =
      completionExtension endpoint conductance nonnegative (first + second) := by
    exact congrArg DFunLike.coe (map_add (completionExtensionLinear endpoint conductance nonnegative resistanceBound) first second).symm
  rw [sumIdentity, completionExtension_limitingEnergy endpoint conductance nonnegative resistanceBound,
    completionExtension_limitingEnergy endpoint conductance nonnegative resistanceBound,
    completionExtension_limitingEnergy endpoint conductance nonnegative resistanceBound]
  rfl

include monotone resistanceBound in
theorem completionExtension_strongly_local
    (mesh : ℕ → ℝ) (meshZero : Tendsto mesh atTop (𝓝 0))
    (edgeBound : ∀ depth edge, conductance depth edge ≠ 0 →
      dist (endpoint depth edge).1 (endpoint depth edge).2 ≤ mesh depth)
    (first second : energyDomain endpoint conductance nonnegative)
    (neighborhood : Set (UniformSpace.Completion Carrier)) (openNeighborhood : IsOpen neighborhood)
    (supportCompact : IsCompact (closure (Function.support
      (completionExtension endpoint conductance nonnegative second : UniformSpace.Completion Carrier → ℝ))))
    (supportSubset : closure (Function.support
      (completionExtension endpoint conductance nonnegative second : UniformSpace.Completion Carrier → ℝ)) ⊆ neighborhood)
    (constant : ∀ firstPoint ∈ neighborhood, ∀ lastPoint ∈ neighborhood,
      completionExtension endpoint conductance nonnegative first firstPoint =
        completionExtension endpoint conductance nonnegative first lastPoint) :
    limitingPairing endpoint conductance first.val second.val = 0 := by
  rw [← completionExtension_limitingPairing endpoint conductance nonnegative resistanceBound]
  apply limitingPairing_strongly_local (completionEnergyEndpoint endpoint) conductance nonnegative
    (completion_traceEnergy_monotone endpoint conductance monotone) mesh meshZero
    (fun depth edge nonzero => ?_)
    (completionExtension_energyDomain endpoint conductance nonnegative resistanceBound first)
    (completionExtension_energyDomain endpoint conductance nonnegative resistanceBound second)
    neighborhood openNeighborhood supportCompact supportSubset constant
  change dist ((endpoint depth edge).1 : UniformSpace.Completion Carrier)
    ((endpoint depth edge).2 : UniformSpace.Completion Carrier) ≤ _
  rw [UniformSpace.Completion.dist_eq]
  exact edgeBound depth edge nonzero

end
end IGSIII34.ResistanceLimit
