import IGSIII34.Forms.HilbertTraceReconstruction
import IGSIII34.ResistanceLimit.LimitEnergy

/-! Uniqueness of the supremum-trace domain and energy among complete
anchored function Hilbert spaces having the same finite trace minima. -/
set_option autoImplicit false
set_option maxHeartbeats 1800000
namespace IGSIII34.Forms
noncomputable section
open IGSIII34.ResistanceLimit Filter Set
open scoped Topology

theorem bounded_trace_with_anchor_iff
    (trace : ℕ → ℝ) (constant : ℝ) :
    BddAbove (Set.range (fun depth => trace depth + constant)) ↔
      BddAbove (Set.range trace) := by
  constructor
  · rintro ⟨bound, bounded⟩
    refine ⟨bound - constant, ?_⟩
    rintro value ⟨depth, rfl⟩
    have below := bounded (Set.mem_range_self depth)
    linarith
  · rintro ⟨bound, bounded⟩
    refine ⟨bound + constant, ?_⟩
    rintro value ⟨depth, rfl⟩
    have below := bounded (Set.mem_range_self depth)
    linarith

theorem finite_trace_form_unique
    {Carrier Energy : Type*} {Edge : ℕ → Type*} [∀ depth, Fintype (Edge depth)]
    [NormedAddCommGroup Energy] [InnerProductSpace ℝ Energy] [CompleteSpace Energy]
    (endpoint : ∀ depth, Edge depth → Carrier × Carrier)
    (conductance : ∀ depth, Edge depth → ℝ)
    (nonnegative : ∀ depth edge, 0 ≤ conductance depth edge)
    (monotone : ∀ potential, Monotone (fun depth => traceEnergy endpoint conductance depth potential))
    (anchor : Carrier) (evaluation : Energy →ₗ[ℝ] (Carrier → ℝ))
    (injective : Function.Injective evaluation)
    (continuous : ∀ point, Continuous (fun potential => evaluation potential point))
    (sites : ℕ → Set Carrier) (nested : Monotone sites)
    (exhaustive : ∀ point, ∃ depth, point ∈ sites depth)
    (lower : ∀ boundary depth potential,
      (∀ point ∈ sites depth, evaluation potential point = boundary point) →
      traceEnergy endpoint conductance depth boundary + boundary anchor ^ 2 ≤ ‖potential‖ ^ 2)
    (attained : ∀ boundary depth, ∃ potential,
      (∀ point ∈ sites depth, evaluation potential point = boundary point) ∧
      ‖potential‖ ^ 2 = traceEnergy endpoint conductance depth boundary + boundary anchor ^ 2) :
    Set.range evaluation = (energyDomain endpoint conductance nonnegative : Set (Carrier → ℝ)) ∧
      ∀ potential, ‖potential‖ ^ 2 - evaluation potential anchor ^ 2 =
        limitingEnergy endpoint conductance (evaluation potential) := by
  have rangeEquality : Set.range evaluation =
      (energyDomain endpoint conductance nonnegative : Set (Carrier → ℝ)) := by
    ext boundary
    rw [hilbert_trace_range_characterization evaluation continuous sites nested exhaustive boundary
      (fun depth => traceEnergy endpoint conductance depth boundary + boundary anchor ^ 2)
      (lower boundary) (attained boundary), bounded_trace_with_anchor_iff]
    rfl
  refine ⟨rangeEquality, ?_⟩
  intro potential
  have finite : evaluation potential ∈ energyDomain endpoint conductance nonnegative := by
    change evaluation potential ∈ (energyDomain endpoint conductance nonnegative : Set (Carrier → ℝ))
    rw [← rangeEquality]
    exact Set.mem_range_self potential
  have normSquare := hilbert_energy_determined_by_traces evaluation injective continuous sites nested exhaustive
    potential (fun depth => traceEnergy endpoint conductance depth (evaluation potential) + evaluation potential anchor ^ 2)
    (lower (evaluation potential)) (attained (evaluation potential))
  have bounded : BddAbove (Set.range (fun depth =>
      traceEnergy endpoint conductance depth (evaluation potential) + evaluation potential anchor ^ 2)) :=
    (bounded_trace_with_anchor_iff _ _).mpr finite
  have supremumLimit := tendsto_atTop_ciSup
    (show Monotone (fun depth => traceEnergy endpoint conductance depth (evaluation potential) + evaluation potential anchor ^ 2) from by
      intro first second ordered
      have below := monotone (evaluation potential) ordered
      dsimp only
      linarith) bounded
  have energyLimit := (traceEnergy_tendsto endpoint conductance nonnegative finite (monotone _)).add_const
    (evaluation potential anchor ^ 2)
  have equality := tendsto_nhds_unique supremumLimit energyLimit
  rw [normSquare, equality]
  ring

end
end IGSIII34.Forms
