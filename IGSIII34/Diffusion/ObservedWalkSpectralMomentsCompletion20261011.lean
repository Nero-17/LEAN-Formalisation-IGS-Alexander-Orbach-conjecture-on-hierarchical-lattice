import IGSIII34.Diffusion.DiscreteRescaledObservationCompletion20261011
import IGSIII34.Diffusion.ObservedCorrectorIntegralCompletion20261011
import IGSIII34.Diffusion.FiniteWalkEulerExpectationLimitCompletion20261011
import IGSIII34.Diffusion.FiniteContinuousPastCompletion20261011

set_option autoImplicit false
set_option maxHeartbeats 4000000
namespace IGSIII34.Diffusion
noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped _root_.Topology NNReal

/-- True finite-walk laws identify the paired spectral moments of every
countable observation limit. The argument uses exact full-past conditional
expectations and uniformly converging resolvent correctors. -/
theorem discrete_walk_limit_paired_spectral_moments_completion20261011
    {Space : Type*} [MetricSpace Space] [CompactSpace Space] [MeasurableSpace Space] [BorelSpace Space]
    (Vertices Edges : ℕ → Type*) [∀ depth, Fintype (Vertices depth)] [∀ depth, DecidableEq (Vertices depth)]
    [∀ depth, Nonempty (Vertices depth)] [∀ depth, MeasurableSpace (Vertices depth)]
    [∀ depth, MeasurableSingletonClass (Vertices depth)] [∀ depth, StandardBorelSpace (Vertices depth)] [∀ depth, Fintype (Edges depth)]
    (endpoint : ∀ depth, Edges depth → Vertices depth × Vertices depth)
    (positiveDegree : ∀ depth vertex, 0 < degree (endpoint depth) vertex)
    (initial : ∀ depth, ProbabilityMeasure (Vertices depth)) (placement : ∀ depth, Vertices depth → Space)
    (scales : ℕ → ℝ) (scalePositive : ∀ depth, 0 < scales depth) (diverges : Tendsto scales atTop atTop)
    (times : ℕ → ℝ≥0) (limitLaw : ProbabilityMeasure (ℕ → Space))
    (weak : Tendsto (fun depth => discreteRescaledObservationLawCompletion20261011 (endpoint depth) (positiveDegree depth)
      (initial depth) (scales depth) times (placement depth)) atTop (𝓝 limitLaw))
    (target : C(Space, ℝ)) (eigenvalue : ℝ) (eigenvalueNonnegative : 0 ≤ eigenvalue)
    (correctors errors : ∀ depth, Vertices depth → ℝ)
    (generator : ∀ depth vertex, scales depth * rateOneGenerator (endpoint depth) (correctors depth) vertex =
      -eigenvalue * correctors depth vertex + errors depth vertex)
    (uniformCorrectors : ∀ tolerance : ℝ, 0 < tolerance → ∀ᶠ depth in atTop,
      ∀ vertex, |correctors depth vertex - target (placement depth vertex)| < tolerance)
    (uniformErrors : ∀ tolerance : ℝ, 0 < tolerance → ∀ᶠ depth in atTop, ∀ vertex, |errors depth vertex| < tolerance)
    {count : ℕ} (pastCoordinates : Fin count → ℕ) (startCoordinate futureCoordinate : ℕ)
    (before : ∀ index, times (pastCoordinates index) ≤ times startCoordinate)
    (ordered : times startCoordinate ≤ times futureCoordinate)
    (past : C((Fin count → Space), ℝ)) :
    (∫ path : ℕ → Space, past (fun index => path (pastCoordinates index)) * target (path futureCoordinate) ∂limitLaw) =
      Real.exp (-eigenvalue * ((times futureCoordinate : ℝ) - times startCoordinate)) *
        (∫ path : ℕ → Space, past (fun index => path (pastCoordinates index)) * target (path startCoordinate) ∂limitLaw) := by
  let starts := fun depth => ⌊scales depth * (times startCoordinate : ℝ)⌋₊
  let steps := fun depth => ⌊scales depth * (times futureCoordinate : ℝ)⌋₊ - starts depth
  let observations := fun depth => discreteRescaledObservationCompletion20261011 (scales depth) times (placement depth)
  let laws := fun depth => discreteWalkProbabilityCompletion20261011 (endpoint depth) (positiveDegree depth) (initial depth)
  let pastTests := fun depth => finiteContinuousPastCompletion20261011 past
    (fun index => ⌊scales depth * (times (pastCoordinates index) : ℝ)⌋₊) (placement depth)
  have known (depth step : ℕ) : StronglyMeasurable[Filtration.piLE (starts depth + step)] (pastTests depth) := by
    apply finiteContinuousPast_known_completion20261011 past _ (placement depth) (measurable_of_finite _) (starts depth + step)
    intro index
    have realBefore : (times (pastCoordinates index) : ℝ) ≤ times startCoordinate := by exact_mod_cast before index
    have floorBefore := Nat.floor_mono (mul_le_mul_of_nonneg_left realBefore (scalePositive depth).le)
    exact floorBefore.trans (Nat.le_add_right _ _)
  have pastLp (depth : ℕ) : MemLp (pastTests depth) 2 (laws depth : Measure (ℕ → Vertices depth)) :=
    finiteContinuousPast_memLp_completion20261011 _ past _ (placement depth) (measurable_of_finite _) 2
  have boundedPast (depth : ℕ) (path : ℕ → Vertices depth) : |pastTests depth path| ≤ ‖past‖ := by
    simpa only [pastTests, finiteContinuousPastCompletion20261011, Real.norm_eq_abs] using past.norm_coe_le_norm
      (fun index => placement depth (path ⌊scales depth * (times (pastCoordinates index) : ℝ)⌋₊))
  have pairedLimit (coordinate : ℕ) : Tendsto
      (fun depth => ∫ path, pastTests depth path * correctors depth (path ⌊scales depth * (times coordinate : ℝ)⌋₊) ∂(laws depth)) atTop
      (𝓝 (∫ path : ℕ → Space, past (fun index => path (pastCoordinates index)) * target (path coordinate) ∂limitLaw)) := by
    apply observed_corrector_paired_integral_tendsto_completion20261011 (fun depth => ℕ → Vertices depth) laws observations
      (fun depth => discreteRescaledObservation_measurable_completion20261011 (scales depth) times (placement depth))
      limitLaw weak pastCoordinates coordinate past target
      (fun depth path => correctors depth (path ⌊scales depth * (times coordinate : ℝ)⌋₊))
    · intro depth
      exact memLp_one_iff_integrable.mp ((finitePathPotential_memLp_completion20261011 (laws depth : Measure (ℕ → Vertices depth))
        (correctors depth) ⌊scales depth * (times coordinate : ℝ)⌋₊ 2).mul (pastLp depth))
    · intro tolerance positive
      filter_upwards [uniformCorrectors tolerance positive] with depth close
      intro path
      exact close _
  have realOrdered : (times startCoordinate : ℝ) ≤ times futureCoordinate := by exact_mod_cast ordered
  have durationNonnegative : 0 ≤ (times futureCoordinate : ℝ) - times startCoordinate := sub_nonneg.mpr realOrdered
  have timeIdentity : (times startCoordinate : ℝ) + ((times futureCoordinate : ℝ) - times startCoordinate) = times futureCoordinate := by ring
  have timeLimit : Tendsto (fun depth => (steps depth : ℝ) / scales depth) atTop
      (𝓝 ((times futureCoordinate : ℝ) - times startCoordinate)) := by
    simpa only [steps, starts, timeIdentity] using eigenEuler_shifted_floor_time_tendsto_completion20261011 scales scalePositive diverges
      (times startCoordinate) ((times futureCoordinate : ℝ) - times startCoordinate) (times startCoordinate).property durationNonnegative
  have futureIdentity (depth : ℕ) : starts depth + steps depth = ⌊scales depth * (times futureCoordinate : ℝ)⌋₊ := by
    have floorBefore := Nat.floor_mono (mul_le_mul_of_nonneg_left realOrdered (scalePositive depth).le)
    dsimp only [starts, steps]
    omega
  have eulerLimit := finite_walk_paired_euler_tendsto_completion20261011 Vertices Edges endpoint positiveDegree initial correctors errors
    scales scalePositive diverges eigenvalue eigenvalueNonnegative generator uniformErrors pastTests starts steps known pastLp
    ‖past‖ (norm_nonneg _) boundedPast ((times futureCoordinate : ℝ) - times startCoordinate) _ timeLimit (pairedLimit startCoordinate)
  have futureLimit : Tendsto
      (fun depth => ∫ path, pastTests depth path * correctors depth (path ⌊scales depth * (times futureCoordinate : ℝ)⌋₊) ∂(laws depth)) atTop
      (𝓝 (Real.exp (-eigenvalue * ((times futureCoordinate : ℝ) - times startCoordinate)) *
        (∫ path : ℕ → Space, past (fun index => path (pastCoordinates index)) * target (path startCoordinate) ∂limitLaw))) := by
    simpa only [futureIdentity, laws, discreteWalkProbabilityCompletion20261011, ProbabilityMeasure.coe_mk] using eulerLimit
  exact tendsto_nhds_unique (pairedLimit futureCoordinate) futureLimit

end
end IGSIII34.Diffusion

