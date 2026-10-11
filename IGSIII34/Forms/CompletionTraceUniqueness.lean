import IGSIII34.Forms.FiniteTraceUniqueness
import IGSIII34.Forms.CompletionExtension

/-! Finite trace uniqueness also determines the entire domain of continuous
functions on the metric completion, not only functions on its dense skeleton. -/
set_option autoImplicit false
set_option maxHeartbeats 1800000
namespace IGSIII34.Forms
noncomputable section
open IGSIII34.ResistanceLimit

def completedFunctionRestriction
    {Carrier Energy : Type*} [MetricSpace Carrier]
    [AddCommGroup Energy] [Module ℝ Energy]
    (evaluation : Energy →ₗ[ℝ] (UniformSpace.Completion Carrier → ℝ)) :
    Energy →ₗ[ℝ] (Carrier → ℝ) where
  toFun potential point := evaluation potential (point : UniformSpace.Completion Carrier)
  map_add' first last := by ext point; simp
  map_smul' scalar potential := by ext point; simp

theorem completed_form_unique_from_finite_traces
    {Carrier Energy : Type*} [MetricSpace Carrier]
    {Edge : ℕ → Type*} [∀ depth, Fintype (Edge depth)]
    [NormedAddCommGroup Energy] [InnerProductSpace ℝ Energy] [CompleteSpace Energy]
    (endpoint : ∀ depth, Edge depth → Carrier × Carrier)
    (conductance : ∀ depth, Edge depth → ℝ)
    (nonnegative : ∀ depth edge, 0 ≤ conductance depth edge)
    (monotone : ∀ potential, Monotone (fun depth => traceEnergy endpoint conductance depth potential))
    (anchor : Carrier)
    (evaluation : Energy →ₗ[ℝ] (UniformSpace.Completion Carrier → ℝ))
    (injective : Function.Injective evaluation)
    (spatialContinuous : ∀ potential, Continuous (evaluation potential))
    (evaluationContinuous : ∀ point, Continuous (fun potential => evaluation potential point))
    (sites : ℕ → Set Carrier) (nested : Monotone sites)
    (exhaustive : ∀ point, ∃ depth, point ∈ sites depth)
    (lower : ∀ boundary depth potential,
      (∀ point ∈ sites depth, evaluation potential (point : UniformSpace.Completion Carrier) = boundary point) →
      traceEnergy endpoint conductance depth boundary + boundary anchor ^ 2 ≤ ‖potential‖ ^ 2)
    (attained : ∀ boundary depth, ∃ potential,
      (∀ point ∈ sites depth, evaluation potential (point : UniformSpace.Completion Carrier) = boundary point) ∧
      ‖potential‖ ^ 2 = traceEnergy endpoint conductance depth boundary + boundary anchor ^ 2) :
    Set.range evaluation = {boundary | Continuous boundary ∧
      (fun point : Carrier => boundary (point : UniformSpace.Completion Carrier)) ∈
        energyDomain endpoint conductance nonnegative} ∧
      ∀ potential, ‖potential‖ ^ 2 - evaluation potential (anchor : UniformSpace.Completion Carrier) ^ 2 =
        limitingEnergy endpoint conductance
          (fun point : Carrier => evaluation potential (point : UniformSpace.Completion Carrier)) := by
  have restrictionInjective : Function.Injective (completedFunctionRestriction evaluation) := by
    intro first last equal
    apply injective
    apply (UniformSpace.Completion.denseRange_coe (α := Carrier)).equalizer
      (spatialContinuous first) (spatialContinuous last)
    exact equal
  have uniqueness := finite_trace_form_unique endpoint conductance nonnegative monotone anchor
    (completedFunctionRestriction evaluation) restrictionInjective
    (fun point => evaluationContinuous (point : UniformSpace.Completion Carrier))
    sites nested exhaustive lower attained
  refine ⟨?_, uniqueness.2⟩
  ext boundary
  constructor
  · rintro ⟨potential, rfl⟩
    refine ⟨spatialContinuous potential, ?_⟩
    change completedFunctionRestriction evaluation potential ∈
      (energyDomain endpoint conductance nonnegative : Set (Carrier → ℝ))
    rw [← uniqueness.1]
    exact Set.mem_range_self potential
  · rintro ⟨continuous, finite⟩
    have member : (fun point : Carrier => boundary (point : UniformSpace.Completion Carrier)) ∈
        Set.range (completedFunctionRestriction evaluation) := by
      rw [uniqueness.1]
      exact finite
    obtain ⟨potential, equal⟩ := member
    refine ⟨potential, ?_⟩
    apply (UniformSpace.Completion.denseRange_coe (α := Carrier)).equalizer
      (spatialContinuous potential) continuous
    exact equal

end
end IGSIII34.Forms
