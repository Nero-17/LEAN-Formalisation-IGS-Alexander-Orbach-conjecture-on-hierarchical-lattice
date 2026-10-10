import IGSIII.Mass.OrientedInnovation
import IGSIII.Mass.StableRecursion
import IGSIII.Mass.ThreeStateMassPerron

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false

namespace Universality.FiniteNetwork

open Matrix

variable {vertices edges : ℕ}

/-- The uniquely determined oriented left coordinates above a three-state
left vector, once the stable orientation direction is resolved. -/
noncomputable def orientedLeftLift (offspring : Matrix MassLiveState MassLiveState ℝ)
    (radius : ℝ) (left : LiveState → ℝ) : MassLiveState → ℝ
  | .connected => left .connected
  | .both => left .both
  | .sourceOnly =>
      (left .connected * offspring .connected .sourceOnly + left .both * offspring .both .sourceOnly +
        left .single * offspring .targetOnly .sourceOnly) /
          (radius - (offspring .sourceOnly .sourceOnly - offspring .targetOnly .sourceOnly))
  | .targetOnly => left .single -
      (left .connected * offspring .connected .sourceOnly + left .both * offspring .both .sourceOnly +
        left .single * offspring .targetOnly .sourceOnly) /
          (radius - (offspring .sourceOnly .sourceOnly - offspring .targetOnly .sourceOnly))

theorem orientedResponse_source_decomposition (network : FiniteNetwork vertices edges)
    (offspring : Matrix MassLiveState MassLiveState ℝ) (state : LiveState)
    (configuration : Configuration edges) :
    network.orientedResponse true (state == .both) configuration
        (offspring *ᵥ (fun child => if child = .sourceOnly then 1 else 0)) =
      (offspring .sourceOnly .sourceOnly - offspring .targetOnly .sourceOnly) *
        network.orientedResponse true (state == .both) configuration
          (fun child => if child = .sourceOnly then 1 else 0) +
      network.liveResponse state configuration
        (fun child => match child with
          | .connected => offspring .connected .sourceOnly
          | .both => offspring .both .sourceOnly
          | .single => offspring .targetOnly .sourceOnly) := by
  simp only [network.orientedResponse_eq, sum_massLiveState, Matrix.mulVec, dotProduct,
    MassLiveState.oriented]
  rw [network.liveResponse_oriented_split]
  simp
  ring

end Universality.FiniteNetwork

namespace Universality.Rule.ConfigurationHistory

open FiniteNetwork Matrix MeasureTheory Filter
open scoped Topology

theorem weightedPopulation_tendsto_of_coordinates (rule : Rule) (state : LiveState)
    (path : Π k, rule.ConfigurationHistory k) (radius multiplier : ℝ) (left values : LiveState → ℝ)
    (coordinates : ∀ child, Tendsto (fun n => weightedPopulation rule state
      (fun parent => if parent = child then 1 else 0) n (path n) / radius ^ n)
        atTop (𝓝 (multiplier * left child))) :
    Tendsto (fun n => weightedPopulation rule state values n (path n) / radius ^ n)
      atTop (𝓝 (multiplier * (left ⬝ᵥ values))) := by
  have convergence := ((coordinates .connected).mul_const (values .connected)).add
    (((coordinates .both).mul_const (values .both)).add ((coordinates .single).mul_const (values .single)))
  convert convergence using 1
  · ext n
    simp only [weightedPopulation_eq_dotProduct, dotProduct, sum_liveState]
    simp
    ring
  · simp only [dotProduct, sum_liveState]
    ring

theorem rootLevelPopulation_unprepend (rule : Rule) (state : LiveState) (values : LiveState → ℝ)
    (path : Π k, rule.ConfigurationHistory k) (radius limit : ℝ) (radius_nonzero : radius ≠ 0)
    (convergence : Tendsto (fun n => rootLevelPopulation rule state values n path / radius ^ n)
      atTop (𝓝 limit)) :
    Tendsto (fun n => weightedPopulation rule state values n (path n) / radius ^ n)
      atTop (𝓝 (radius * limit)) := by
  have shifted := (convergence.comp (tendsto_add_atTop_nat 1)).const_mul radius
  convert shifted using 1
  · ext n
    simp only [Function.comp_apply, rootLevelPopulation_succ, pow_succ]
    field_simp

theorem orientedWeightedPopulation_erase (rule : Rule) (state : LiveState)
    (values : LiveState → ℝ) (n : ℕ) (history : rule.ConfigurationHistory n) :
    orientedWeightedPopulation rule state (fun child => values child.erase) n history =
      weightedPopulation rule state values n history :=
  (rule.generation n).network.orientedResponse_erase state (latest rule n history) values

theorem orientedWeightedPopulation_target_split (rule : Rule) (state : LiveState)
    (n : ℕ) (history : rule.ConfigurationHistory n) :
    orientedWeightedPopulation rule state (fun child => if child = .targetOnly then 1 else 0) n history =
      weightedPopulation rule state (fun child => if child = .single then 1 else 0) n history -
        orientedWeightedPopulation rule state (fun child => if child = .sourceOnly then 1 else 0) n history := by
  unfold orientedWeightedPopulation weightedPopulation
  rw [(rule.generation n).network.liveResponse_oriented_split]
  simp [orientedResponse_eq, sum_massLiveState, MassLiveState.oriented]

noncomputable def rootLevelOrientedPopulation (rule : Rule) (values : MassLiveState → ℝ)
    (n : ℕ) (path : Π k, rule.ConfigurationHistory k) : ℝ :=
  match n with
  | 0 => values .connected
  | k + 1 => orientedWeightedPopulation rule .connected values k (path k)

theorem rootLevelOrientedPopulation_tendsto (rule : Rule) (values : MassLiveState → ℝ)
    (radius : ℝ) (radius_gt_one : 1 < radius) (path : Π k, rule.ConfigurationHistory k) (limit : ℝ)
    (convergence : Tendsto (fun n => orientedWeightedPopulation rule .connected values n (path n) / radius ^ n)
      atTop (𝓝 limit)) :
    Tendsto (fun n => rootLevelOrientedPopulation rule values n path / radius ^ n)
      atTop (𝓝 (limit / radius)) := by
  convert IGSIII.Mass.tendsto_prepend_normalized
    (fun n => orientedWeightedPopulation rule .connected values n (path n)) (values .connected) 0 radius limit
    radius_gt_one convergence using 1
  ext n
  cases n <;> simp [rootLevelOrientedPopulation]

end Universality.Rule.ConfigurationHistory

namespace Universality.Rule

open FiniteNetwork Matrix MeasureTheory Filter
open scoped Topology

/-- The two actual oriented one-arm counts have individual limits on the same
history paths as the three-state population limit. -/
theorem Classical.oriented_population_limit_from_three_state {rule : Rule}
    (classicalRule : rule.Classical) (p : ℝ) (positive : 0 < p) (below_one : p < 1)
    (fixed_point : rule.network.reliability p = p) (left : LiveState → ℝ)
    (limit : (Π k, rule.ConfigurationHistory k) → ℝ)
    (coordinate_limit : ∀ᵐ path ∂ConfigurationHistory.infiniteLaw rule p positive below_one fixed_point true,
      ∀ child : LiveState,
      Tendsto (fun n => ConfigurationHistory.rootLevelPopulation rule .connected
        (fun state => if state = child then 1 else 0) n path /
          ((spectralRadius ℂ ((rule.network.massMatrix p).map Complex.ofReal)).toReal) ^ n)
        atTop (𝓝 (limit path * left child))) :
    ∀ᵐ path ∂ConfigurationHistory.infiniteLaw rule p positive below_one fixed_point true,
      ∀ child : MassLiveState,
      Tendsto (fun n => ConfigurationHistory.rootLevelOrientedPopulation rule
        (fun state => if state = child then 1 else 0) n path /
          ((spectralRadius ℂ ((rule.network.massMatrix p).map Complex.ofReal)).toReal) ^ n)
        atTop (𝓝 (limit path * orientedLeftLift (rule.network.orientedMassMatrix p)
          ((spectralRadius ℂ ((rule.network.massMatrix p).map Complex.ofReal)).toReal) left child)) := by
  have radius_gt_one : 1 < (spectralRadius ℂ ((rule.network.massMatrix p).map Complex.ofReal)).toReal :=
    (rule.network.interior_fixed_point_strictly_unstable p positive below_one fixed_point classicalRule.scale).trans
      (rule.interior_fixed_point_spectral_dominance p positive below_one fixed_point
        classicalRule.massAdmissible.symmetric classicalRule.scale).2.1
  have radius_positive := zero_lt_one.trans radius_gt_one
  have gap := classicalRule.oriented_mass_gap p positive below_one fixed_point
  have denominator_positive : 0 <
      (spectralRadius ℂ ((rule.network.massMatrix p).map Complex.ofReal)).toReal -
        (rule.network.orientedMassMatrix p .sourceOnly .sourceOnly -
          rule.network.orientedMassMatrix p .targetOnly .sourceOnly) := by
    linarith [le_abs_self (rule.network.orientedMassMatrix p .sourceOnly .sourceOnly -
      rule.network.orientedMassMatrix p .targetOnly .sourceOnly)]
  have innovations := classicalRule.oriented_population_innovation_ae_zero p positive below_one fixed_point
    (fun child => if child = .sourceOnly then 1 else 0) .connected
  filter_upwards [coordinate_limit, innovations,
    ConfigurationHistory.infiniteLaw_extends rule p positive below_one fixed_point true] with
    path coordinates innovation_zero coherent
  have ordinary (child : LiveState) := ConfigurationHistory.rootLevelPopulation_unprepend rule .connected
    (fun state => if state = child then 1 else 0) path
    ((spectralRadius ℂ ((rule.network.massMatrix p).map Complex.ofReal)).toReal)
    (limit path * left child) radius_positive.ne' (coordinates child)
  have ordinary_coordinates : ∀ child : LiveState,
      Tendsto (fun n => ConfigurationHistory.weightedPopulation rule .connected
        (fun state => if state = child then 1 else 0) n (path n) /
          ((spectralRadius ℂ ((rule.network.massMatrix p).map Complex.ofReal)).toReal) ^ n)
        atTop (𝓝 (((spectralRadius ℂ ((rule.network.massMatrix p).map Complex.ofReal)).toReal * limit path) * left child)) := by
    intro child
    convert ordinary child using 1 <;> ring
  have forcing_convergence := ConfigurationHistory.weightedPopulation_tendsto_of_coordinates rule .connected path
    ((spectralRadius ℂ ((rule.network.massMatrix p).map Complex.ofReal)).toReal)
    (((spectralRadius ℂ ((rule.network.massMatrix p).map Complex.ofReal)).toReal) * limit path) left
    (fun child => match child with
      | .connected => rule.network.orientedMassMatrix p .connected .sourceOnly
      | .both => rule.network.orientedMassMatrix p .both .sourceOnly
      | .single => rule.network.orientedMassMatrix p .targetOnly .sourceOnly)
    ordinary_coordinates
  have source_convergence := IGSIII.Mass.tendsto_stable_recursion
    (fun n => ConfigurationHistory.orientedWeightedPopulation rule .connected
      (fun child => if child = .sourceOnly then 1 else 0) n (path n) /
        ((spectralRadius ℂ ((rule.network.massMatrix p).map Complex.ofReal)).toReal) ^ n)
    (fun n => (ConfigurationHistory.weightedPopulation rule .connected
      (fun child => match child with
        | .connected => rule.network.orientedMassMatrix p .connected .sourceOnly
        | .both => rule.network.orientedMassMatrix p .both .sourceOnly
        | .single => rule.network.orientedMassMatrix p .targetOnly .sourceOnly) n (path n) /
          ((spectralRadius ℂ ((rule.network.massMatrix p).map Complex.ofReal)).toReal) ^ n +
        ConfigurationHistory.orientedPopulationInnovation rule p .connected
          (fun child => if child = .sourceOnly then 1 else 0) n (path (n + 1)) /
          ((spectralRadius ℂ ((rule.network.massMatrix p).map Complex.ofReal)).toReal) ^ n) /
          ((spectralRadius ℂ ((rule.network.massMatrix p).map Complex.ofReal)).toReal))
    ((rule.network.orientedMassMatrix p .sourceOnly .sourceOnly -
      rule.network.orientedMassMatrix p .targetOnly .sourceOnly) /
        ((spectralRadius ℂ ((rule.network.massMatrix p).map Complex.ofReal)).toReal))
    ((((spectralRadius ℂ ((rule.network.massMatrix p).map Complex.ofReal)).toReal) * limit path) *
      (left ⬝ᵥ (fun child => match child with
        | .connected => rule.network.orientedMassMatrix p .connected .sourceOnly
        | .both => rule.network.orientedMassMatrix p .both .sourceOnly
        | .single => rule.network.orientedMassMatrix p .targetOnly .sourceOnly)) /
          ((spectralRadius ℂ ((rule.network.massMatrix p).map Complex.ofReal)).toReal))
    (by rw [abs_div, abs_of_pos radius_positive]; exact (div_lt_one radius_positive).mpr gap)
    (fun n => by
      unfold ConfigurationHistory.orientedPopulationInnovation
      rw [coherent n]
      unfold ConfigurationHistory.orientedWeightedPopulation
      rw [(rule.generation n).network.orientedResponse_source_decomposition]
      unfold ConfigurationHistory.weightedPopulation
      rw [pow_succ]
      field_simp
      ring)
    (by
      simpa only [add_zero] using
        (forcing_convergence.add innovation_zero).div_const
          ((spectralRadius ℂ ((rule.network.massMatrix p).map Complex.ofReal)).toReal))
  have source_value :
      Tendsto (fun n => ConfigurationHistory.orientedWeightedPopulation rule .connected
        (fun child => if child = .sourceOnly then 1 else 0) n (path n) /
          ((spectralRadius ℂ ((rule.network.massMatrix p).map Complex.ofReal)).toReal) ^ n)
        atTop (𝓝 (((spectralRadius ℂ ((rule.network.massMatrix p).map Complex.ofReal)).toReal * limit path) *
          orientedLeftLift (rule.network.orientedMassMatrix p)
            ((spectralRadius ℂ ((rule.network.massMatrix p).map Complex.ofReal)).toReal) left .sourceOnly)) := by
    convert source_convergence using 1
    congr 1
    simp only [orientedLeftLift, dotProduct, sum_liveState]
    field_simp
  have ordinary_oriented (child : MassLiveState) :
      Tendsto (fun n => ConfigurationHistory.orientedWeightedPopulation rule .connected
        (fun state => if state = child then 1 else 0) n (path n) /
          ((spectralRadius ℂ ((rule.network.massMatrix p).map Complex.ofReal)).toReal) ^ n)
        atTop (𝓝 (((spectralRadius ℂ ((rule.network.massMatrix p).map Complex.ofReal)).toReal * limit path) *
          orientedLeftLift (rule.network.orientedMassMatrix p)
            ((spectralRadius ℂ ((rule.network.massMatrix p).map Complex.ofReal)).toReal) left child)) := by
    cases child with
    | connected =>
      convert ordinary_coordinates .connected using 1
      · ext n
        rw [← ConfigurationHistory.orientedWeightedPopulation_erase]
        congr 2
        ext state
        cases state <;> simp [MassLiveState.erase]
      · rfl
    | both =>
      convert ordinary_coordinates .both using 1
      · ext n
        rw [← ConfigurationHistory.orientedWeightedPopulation_erase]
        congr 2
        ext state
        cases state <;> simp [MassLiveState.erase]
      · rfl
    | sourceOnly => exact source_value
    | targetOnly =>
      have convergence := (ordinary_coordinates .single).sub source_value
      convert convergence using 1
      · ext n
        rw [ConfigurationHistory.orientedWeightedPopulation_target_split]
        ring
      · simp only [orientedLeftLift]
        ring
  intro child
  have convergence := ConfigurationHistory.rootLevelOrientedPopulation_tendsto rule
    (fun state => if state = child then 1 else 0)
    ((spectralRadius ℂ ((rule.network.massMatrix p).map Complex.ofReal)).toReal)
    radius_gt_one path _ (ordinary_oriented child)
  convert convergence using 1
  field_simp

end Universality.Rule
