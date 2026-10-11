import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Topology.Order.MonotoneConvergence
import Mathlib.Topology.MetricSpace.Cauchy

/-! Complete function Hilbert spaces are reconstructed from their finite
trace minima. Completeness and the finite minimisation property, rather than
an assumed trace-exhaustion identity, imply the limiting energy identity. -/
set_option autoImplicit false
set_option maxHeartbeats 1600000
namespace IGSIII34.Forms
noncomputable section
open Filter Set
open scoped Topology

theorem hilbert_trace_reconstruction
    {Carrier Energy : Type*} [NormedAddCommGroup Energy]
    [InnerProductSpace ℝ Energy] [CompleteSpace Energy]
    (evaluation : Energy →ₗ[ℝ] (Carrier → ℝ))
    (evaluationContinuous : ∀ point, Continuous (fun potential => evaluation potential point))
    (sites : ℕ → Set Carrier) (nested : Monotone sites)
    (exhaustive : ∀ point, ∃ depth, point ∈ sites depth)
    (boundary : Carrier → ℝ) (trace : ℕ → ℝ)
    (lower : ∀ depth potential, (∀ point ∈ sites depth, evaluation potential point = boundary point) →
      trace depth ≤ ‖potential‖ ^ 2)
    (attained : ∀ depth, ∃ potential, (∀ point ∈ sites depth, evaluation potential point = boundary point) ∧
      ‖potential‖ ^ 2 = trace depth)
    (bounded : BddAbove (Set.range trace)) :
    ∃ potential, evaluation potential = boundary ∧ ‖potential‖ ^ 2 = ⨆ depth, trace depth := by
  choose sequence agrees normSquare using attained
  have increasing : Monotone trace := by
    intro first second ordered
    rw [← normSquare second]
    exact lower first (sequence second) (fun point member => agrees second point (nested ordered member))
  have traceLimit := tendsto_atTop_ciSup increasing bounded
  have sequenceCauchy : CauchySeq sequence := by
    apply Metric.cauchySeq_iff.mpr
    intro epsilon positive
    have close := (Metric.tendsto_atTop.mp traceLimit) (epsilon ^ 2 / 8) (by positivity)
    obtain ⟨threshold, close⟩ := close
    refine ⟨threshold, ?_⟩
    intro first firstAfter second secondAfter
    have midpointBound := lower threshold ((1 / 2 : ℝ) • (sequence first + sequence second)) (by
      intro point member
      simp only [map_smul, map_add, Pi.smul_apply, Pi.add_apply, smul_eq_mul,
        agrees first point (nested firstAfter member), agrees second point (nested secondAfter member)]
      ring)
    have midpointNorm : ‖(1 / 2 : ℝ) • (sequence first + sequence second)‖ ^ 2 =
        (1 / 4 : ℝ) * ‖sequence first + sequence second‖ ^ 2 := by
      rw [norm_smul]
      norm_num
      ring
    rw [midpointNorm] at midpointBound
    have parallelogram := parallelogram_law_with_norm ℝ (sequence first) (sequence second)
    rw [normSquare first, normSquare second] at parallelogram
    have firstBound : trace first ≤ ⨆ depth, trace depth := le_ciSup bounded first
    have secondBound : trace second ≤ ⨆ depth, trace depth := le_ciSup bounded second
    have thresholdBound := close threshold le_rfl
    rw [Real.dist_eq] at thresholdBound
    have difference := (abs_lt.mp thresholdBound).1
    rw [dist_eq_norm]
    nlinarith [norm_nonneg (sequence first - sequence second)]
  obtain ⟨potential, convergence⟩ := cauchySeq_tendsto_of_complete sequenceCauchy
  refine ⟨potential, ?_, ?_⟩
  · funext point
    obtain ⟨threshold, member⟩ := exhaustive point
    have eventuallyEqual : ∀ᶠ depth in atTop, evaluation (sequence depth) point = boundary point := by
      filter_upwards [eventually_ge_atTop threshold] with depth after
      exact agrees depth point (nested after member)
    have boundaryLimit : Tendsto (fun depth => evaluation (sequence depth) point) atTop (𝓝 (boundary point)) :=
      tendsto_const_nhds.congr' (eventuallyEqual.mono (fun _ equality => equality.symm))
    exact tendsto_nhds_unique ((evaluationContinuous point).tendsto potential |>.comp convergence) boundaryLimit
  · have normLimit := convergence.norm.pow 2
    simp_rw [normSquare] at normLimit
    exact tendsto_nhds_unique normLimit traceLimit

theorem hilbert_energy_determined_by_traces
    {Carrier Energy : Type*} [NormedAddCommGroup Energy]
    [InnerProductSpace ℝ Energy] [CompleteSpace Energy]
    (evaluation : Energy →ₗ[ℝ] (Carrier → ℝ))
    (evaluationInjective : Function.Injective evaluation)
    (evaluationContinuous : ∀ point, Continuous (fun potential => evaluation potential point))
    (sites : ℕ → Set Carrier) (nested : Monotone sites)
    (exhaustive : ∀ point, ∃ depth, point ∈ sites depth)
    (potential : Energy) (trace : ℕ → ℝ)
    (lower : ∀ depth candidate, (∀ point ∈ sites depth, evaluation candidate point = evaluation potential point) →
      trace depth ≤ ‖candidate‖ ^ 2)
    (attained : ∀ depth, ∃ candidate,
      (∀ point ∈ sites depth, evaluation candidate point = evaluation potential point) ∧
      ‖candidate‖ ^ 2 = trace depth) :
    ‖potential‖ ^ 2 = ⨆ depth, trace depth := by
  have bounded : BddAbove (Set.range trace) := ⟨‖potential‖ ^ 2, by
    rintro value ⟨depth, rfl⟩
    exact lower depth potential (fun _ _ => rfl)⟩
  obtain ⟨reconstructed, equality, normSquare⟩ := hilbert_trace_reconstruction evaluation
    evaluationContinuous sites nested exhaustive (evaluation potential) trace lower attained bounded
  exact (congrArg (fun candidate : Energy => ‖candidate‖ ^ 2) (evaluationInjective equality)).symm.trans normSquare

theorem hilbert_trace_range_characterization
    {Carrier Energy : Type*} [NormedAddCommGroup Energy]
    [InnerProductSpace ℝ Energy] [CompleteSpace Energy]
    (evaluation : Energy →ₗ[ℝ] (Carrier → ℝ))
    (evaluationContinuous : ∀ point, Continuous (fun potential => evaluation potential point))
    (sites : ℕ → Set Carrier) (nested : Monotone sites)
    (exhaustive : ∀ point, ∃ depth, point ∈ sites depth)
    (boundary : Carrier → ℝ) (trace : ℕ → ℝ)
    (lower : ∀ depth potential, (∀ point ∈ sites depth, evaluation potential point = boundary point) →
      trace depth ≤ ‖potential‖ ^ 2)
    (attained : ∀ depth, ∃ potential, (∀ point ∈ sites depth, evaluation potential point = boundary point) ∧
      ‖potential‖ ^ 2 = trace depth) :
    boundary ∈ Set.range evaluation ↔ BddAbove (Set.range trace) := by
  constructor
  · rintro ⟨potential, rfl⟩
    refine ⟨‖potential‖ ^ 2, ?_⟩
    rintro value ⟨depth, rfl⟩
    exact lower depth potential (fun _ _ => rfl)
  · intro bounded
    obtain ⟨potential, equality, _⟩ := hilbert_trace_reconstruction evaluation
      evaluationContinuous sites nested exhaustive boundary trace lower attained bounded
    exact ⟨potential, equality⟩

/-- Two complete function Hilbert spaces with the same finite trace minima
have precisely the same functions and squared norms. The hypotheses state
the finite minimisation problems, not the desired limiting norm identity. -/
theorem complete_function_hilbert_spaces_unique_from_traces
    {Carrier First Second : Type*}
    [NormedAddCommGroup First] [InnerProductSpace ℝ First] [CompleteSpace First]
    [NormedAddCommGroup Second] [InnerProductSpace ℝ Second] [CompleteSpace Second]
    (firstEvaluation : First →ₗ[ℝ] (Carrier → ℝ))
    (secondEvaluation : Second →ₗ[ℝ] (Carrier → ℝ))
    (firstInjective : Function.Injective firstEvaluation)
    (secondInjective : Function.Injective secondEvaluation)
    (firstContinuous : ∀ point, Continuous (fun potential => firstEvaluation potential point))
    (secondContinuous : ∀ point, Continuous (fun potential => secondEvaluation potential point))
    (sites : ℕ → Set Carrier) (nested : Monotone sites)
    (exhaustive : ∀ point, ∃ depth, point ∈ sites depth)
    (trace : (Carrier → ℝ) → ℕ → ℝ)
    (firstLower : ∀ boundary depth potential,
      (∀ point ∈ sites depth, firstEvaluation potential point = boundary point) →
        trace boundary depth ≤ ‖potential‖ ^ 2)
    (secondLower : ∀ boundary depth potential,
      (∀ point ∈ sites depth, secondEvaluation potential point = boundary point) →
        trace boundary depth ≤ ‖potential‖ ^ 2)
    (firstAttained : ∀ boundary depth, ∃ potential,
      (∀ point ∈ sites depth, firstEvaluation potential point = boundary point) ∧
        ‖potential‖ ^ 2 = trace boundary depth)
    (secondAttained : ∀ boundary depth, ∃ potential,
      (∀ point ∈ sites depth, secondEvaluation potential point = boundary point) ∧
        ‖potential‖ ^ 2 = trace boundary depth) :
    Set.range firstEvaluation = Set.range secondEvaluation ∧
      ∀ first second, firstEvaluation first = secondEvaluation second → ‖first‖ ^ 2 = ‖second‖ ^ 2 := by
  constructor
  · ext boundary
    rw [hilbert_trace_range_characterization firstEvaluation firstContinuous sites nested exhaustive
      boundary (trace boundary) (firstLower boundary) (firstAttained boundary),
      hilbert_trace_range_characterization secondEvaluation secondContinuous sites nested exhaustive
      boundary (trace boundary) (secondLower boundary) (secondAttained boundary)]
  · intro first second equality
    rw [hilbert_energy_determined_by_traces firstEvaluation firstInjective firstContinuous sites nested exhaustive
      first (trace (firstEvaluation first)) (firstLower _) (firstAttained _),
      hilbert_energy_determined_by_traces secondEvaluation secondInjective secondContinuous sites nested exhaustive
      second (trace (secondEvaluation second)) (secondLower _) (secondAttained _), equality]

end
end IGSIII34.Forms
