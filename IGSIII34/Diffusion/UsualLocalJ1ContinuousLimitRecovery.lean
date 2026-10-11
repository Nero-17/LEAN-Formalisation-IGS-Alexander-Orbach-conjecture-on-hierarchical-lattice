import IGSIII34.Diffusion.CadlagContinuityEndpoints

set_option autoImplicit false
set_option maxHeartbeats 3800000
set_option backward.isDefEq.respectTransparency false
namespace IGSIII34.Diffusion
noncomputable section
open Filter Set
open scoped Topology NNReal ENNReal
variable {Space : Type*} [MetricSpace Space] [CompactSpace Space]

/-- A continuous reference controls uniform distance even when the
centre of the J1 neighbourhood has jumps. -/
theorem intervalJ1_continuous_reference_neighbourhood
    (reference : C(SkorokhodIntervalTimeCompletion20261011, Space))
    (centre : SkorokhodIntervalPathCompletion20261011 Space)
    (bound : ℝ) (bounded : ∀ time, dist (centre time) (reference time) ≤ bound)
    (tolerance : ℝ) (positive : 0 < tolerance) :
    ∃ error : ℝ, 0 < error ∧ ∀ candidate : SkorokhodIntervalPathCompletion20261011 Space,
      dist candidate centre < error →
        ∀ time, dist (candidate time) (reference time) < bound + tolerance := by
  obtain ⟨duration, durationPositive, continuousClose⟩ := Metric.uniformContinuous_iff.mp
    (CompactSpace.uniformContinuous_of_continuous reference.continuous) (tolerance / 2) (by positivity)
  let error : ℝ := min duration (tolerance / 2)
  have errorPositive : 0 < error := lt_min durationPositive (by positivity)
  refine ⟨error, errorPositive, ?_⟩
  intro candidate near time
  have nearEDistance : skorokhodJ1EDistCompletion20261011 candidate centre < ENNReal.ofReal error :=
    edist_lt_ofReal.mpr near
  obtain ⟨change, changeSmall⟩ := iInf_lt_iff.mp nearEDistance
  have timeSmall : dist (change (change.symm time)) (change.symm time) < error := by
    apply edist_lt_ofReal.mp
    exact ((le_iSup (fun next => edist (change next) next) (change.symm time)).trans
      (le_max_left _ _)).trans_lt changeSmall
  have spatialSmall : dist (candidate (change (change.symm time))) (centre (change.symm time)) < error := by
    apply edist_lt_ofReal.mp
    exact ((le_iSup (fun next => edist (candidate (change next)) (centre next)) (change.symm time)).trans
      (le_max_right _ _)).trans_lt changeSmall
  rw [change.apply_symm_apply] at timeSmall spatialSmall
  have inverseTime : dist (change.symm time) time < duration := by
    rw [dist_comm] at timeSmall
    exact timeSmall.trans_le (min_le_left _ _)
  have continuousNear := continuousClose inverseTime
  have triangle := (dist_triangle (candidate time) (centre (change.symm time)) (reference time)).trans
    (add_le_add le_rfl (dist_triangle (centre (change.symm time)) (reference (change.symm time)) (reference time)))
  have centreBound := bounded (change.symm time)
  have errorBound : error ≤ tolerance / 2 := min_le_right _ _
  linarith

theorem physicalIntervalTime_before_horizon
    (horizon : ℝ≥0) (time : SkorokhodIntervalTimeCompletion20261011) :
    horizon * ⟨time.val, time.property.1⟩ ≤ horizon := by
  apply NNReal.coe_le_coe.mp
  simp only [NNReal.coe_mul, NNReal.coe_mk]
  have unitValue : ((⟨time.val, time.property.1⟩ : ℝ≥0) : ℝ) = time.val := rfl
  have upper := time.property.2
  have horizonNonnegative : 0 ≤ (horizon : ℝ) := horizon.property
  have valueBound : (horizon : ℝ) * time.val ≤ (horizon : ℝ) := by nlinarith
  exact (congrArg (fun value : ℝ => (horizon : ℝ) * value) unitValue).le.trans valueBound

/-- Uniform tubes with a spare terminal interval. The spare interval
lets one choose a continuity endpoint of any cadlag centre. -/
def usualLocalJ1ContinuousReferenceTube
    (reference : ℝ≥0 → Space) (horizon : ℝ≥0) (radius : ℝ) :
    Set (SkorokhodCadlagPathCompletion20261011 Space) :=
  {path | ∃ terminal : ℝ≥0, horizon < terminal ∧ ∃ bound : ℝ, bound < radius ∧
    ∀ time : ℝ≥0, time ≤ terminal → dist (path.val time) (reference time) ≤ bound}

theorem usualLocalJ1ContinuousReferenceTube_isOpen
    (reference : ℝ≥0 → Space) (continuous : Continuous reference)
    (horizon : ℝ≥0) (radius : ℝ) :
    @IsOpen (SkorokhodCadlagPathCompletion20261011 Space) usualLocalJ1SequenceTopology
      (usualLocalJ1ContinuousReferenceTube reference horizon radius) := by
  intro paths path convergence membership
  obtain ⟨terminal, terminalAfter, bound, boundBelow, uniformBound⟩ := membership
  obtain ⟨endpoint, endpointAfter, endpointBefore, endpointContinuous⟩ :=
    cadlag_exists_continuity_endpoint path horizon terminal terminalAfter
  let profile : C(SkorokhodIntervalTimeCompletion20261011, Space) :=
    ⟨fun time => reference (endpoint * ⟨time.val, time.property.1⟩), continuous.comp (by fun_prop)⟩
  have profileBound : ∀ time, dist
      (skorokhodHorizonRestrictionCompletion20261011 endpoint path.val time) (profile time) ≤ bound := by
    intro time
    exact uniformBound _ ((physicalIntervalTime_before_horizon endpoint time).trans endpointBefore.le)
  let tolerance : ℝ := (radius - bound) / 2
  have tolerancePositive : 0 < tolerance := by dsimp [tolerance]; linarith
  obtain ⟨error, errorPositive, neighbourhoodBound⟩ := intervalJ1_continuous_reference_neighbourhood
    profile (skorokhodHorizonRestrictionCompletion20261011 endpoint path.val) bound profileBound
    tolerance tolerancePositive
  have profileConvergence := convergence endpoint endpointContinuous
  filter_upwards [profileConvergence.eventually (Metric.ball_mem_nhds _ errorPositive)] with index near
  refine ⟨endpoint, endpointAfter, bound + tolerance, ?_, ?_⟩
  · dsimp [tolerance]
    linarith
  · intro time before
    have endpointPositive : 0 < (endpoint : ℝ) :=
      lt_of_le_of_lt horizon.property (NNReal.coe_lt_coe.mpr endpointAfter)
    let unitTime : SkorokhodIntervalTimeCompletion20261011 :=
      ⟨(time : ℝ) / (endpoint : ℝ),
        ⟨div_nonneg time.property endpointPositive.le,
          (div_le_one endpointPositive).mpr (NNReal.coe_le_coe.mpr before)⟩⟩
    have physicalTime : endpoint * ⟨unitTime.val, unitTime.property.1⟩ = time := by
      apply NNReal.eq
      simp only [NNReal.coe_mul, NNReal.coe_mk]
      exact mul_div_cancel₀ _ endpointPositive.ne'
    have value := neighbourhoodBound (skorokhodHorizonRestrictionCompletion20261011 endpoint (paths index).val)
      near unitTime
    change dist ((paths index).val (endpoint * ⟨unitTime.val, unitTime.property.1⟩))
      (reference (endpoint * ⟨unitTime.val, unitTime.property.1⟩)) < bound + tolerance at value
    rw [physicalTime] at value
    exact value.le

/-- Convergence in the constructed local topology to a continuous path
recovers uniform convergence on every finite physical-time window. -/
theorem usualLocalJ1_topology_continuous_limit_uniform
    {Index : Type*} {along : Filter Index}
    (paths : Index → SkorokhodCadlagPathCompletion20261011 Space)
    (path : SkorokhodCadlagPathCompletion20261011 Space)
    (continuous : Continuous path.val.toFun)
    (convergence : Tendsto paths along (@nhds _ usualLocalJ1SequenceTopology path))
    (horizon : ℝ≥0) (radius : ℝ) (positive : 0 < radius) :
    ∀ᶠ index in along, ∀ time : ℝ≥0, time ≤ horizon →
      dist ((paths index).val time) (path.val time) < radius := by
  have inside : path ∈ usualLocalJ1ContinuousReferenceTube path.val.toFun horizon radius := by
    refine ⟨horizon + 1, by simp, 0, positive, ?_⟩
    intro time before
    simp
  have neighbourhood : usualLocalJ1ContinuousReferenceTube path.val.toFun horizon radius ∈
      @nhds _ usualLocalJ1SequenceTopology path := by
    letI : TopologicalSpace (SkorokhodCadlagPathCompletion20261011 Space) := usualLocalJ1SequenceTopology
    exact (usualLocalJ1ContinuousReferenceTube_isOpen path.val.toFun continuous horizon radius).mem_nhds inside
  filter_upwards [convergence.eventually neighbourhood] with index membership
  obtain ⟨terminal, terminalAfter, bound, boundBelow, uniformBound⟩ := membership
  intro time before
  exact (uniformBound time (before.trans terminalAfter.le)).trans_lt boundBelow

/-- The full usual-local window criterion is recovered at every
continuous limiting path. This applies to the support of the actual
constructed diffusion laws. -/
theorem usualLocalJ1_topology_tendsto_continuous_limit_criterion
    (paths : ℕ → SkorokhodCadlagPathCompletion20261011 Space)
    (path : SkorokhodCadlagPathCompletion20261011 Space)
    (continuous : Continuous path.val.toFun) :
    Tendsto paths atTop (@nhds _ usualLocalJ1SequenceTopology path) ↔
      usualLocalJ1SequenceConvergence paths path := by
  constructor
  · intro convergence horizon endpointContinuous
    apply Metric.tendsto_nhds.mpr
    intro tolerance positive
    filter_upwards [usualLocalJ1_topology_continuous_limit_uniform paths path continuous convergence
      horizon (tolerance / 2) (by positivity)] with index uniformBound
    have edistance : edist (skorokhodHorizonRestrictionCompletion20261011 horizon (paths index).val)
        (skorokhodHorizonRestrictionCompletion20261011 horizon path.val) ≤ ENNReal.ofReal (tolerance / 2) := by
      apply (skorokhodJ1EDist_le_uniform_completion20261011 _ _).trans
      apply iSup_le
      intro time
      rw [edist_dist]
      exact ENNReal.ofReal_le_ofReal (uniformBound _ (physicalIntervalTime_before_horizon horizon time)).le
    exact ((edist_le_ofReal (by positivity : 0 ≤ tolerance / 2)).mp edistance).trans_lt (by linarith)
  · exact usualLocalJ1Sequence_tendsto paths path

/-- At a continuous path the constructed local topology has exactly
the integer-horizon neighbourhood filter. Thus recovery is valid for
arbitrary filters, not only sequences. -/
theorem usualLocalJ1_continuous_limit_nhds_eq_integer
    (path : SkorokhodCadlagPathCompletion20261011 Space)
    (continuous : Continuous path.val.toFun) :
    @nhds _ usualLocalJ1SequenceTopology path = 𝓝 path := by
  have toInteger : Tendsto (id : SkorokhodCadlagPathCompletion20261011 Space →
      SkorokhodCadlagPathCompletion20261011 Space)
      (@nhds _ usualLocalJ1SequenceTopology path) (𝓝 path) := by
    rw [tendsto_subtype_rng]
    apply skorokhodGlobal_tendsto_iff_completion20261011.mpr
    intro count
    apply Metric.tendsto_nhds.mpr
    intro tolerance positive
    filter_upwards [usualLocalJ1_topology_continuous_limit_uniform id path continuous tendsto_id
      (count + 1 : ℝ≥0) (tolerance / 2) (by positivity)] with candidate uniformBound
    have edistance : edist (skorokhodIntegerProfileCompletion20261011 candidate.val count)
        (skorokhodIntegerProfileCompletion20261011 path.val count) ≤ ENNReal.ofReal (tolerance / 2) := by
      apply (skorokhodJ1EDist_le_uniform_completion20261011 _ _).trans
      apply iSup_le
      intro time
      rw [edist_dist]
      exact ENNReal.ofReal_le_ofReal
        (uniformBound _ (physicalIntervalTime_before_horizon (count + 1 : ℝ≥0) time)).le
    exact ((edist_le_ofReal (by positivity : 0 ≤ tolerance / 2)).mp edistance).trans_lt (by linarith)
  have toLocal : Tendsto (id : SkorokhodCadlagPathCompletion20261011 Space →
      SkorokhodCadlagPathCompletion20261011 Space) (𝓝 path)
      (@nhds _ usualLocalJ1SequenceTopology path) :=
    @Continuous.tendsto (SkorokhodCadlagPathCompletion20261011 Space)
      (SkorokhodCadlagPathCompletion20261011 Space) inferInstance usualLocalJ1SequenceTopology
      id integerJ1_to_usualLocalJ1_identity_continuous path
  exact le_antisymm (by simpa only [Filter.Tendsto, Filter.map_id] using toInteger)
    (by simpa only [Filter.Tendsto, Filter.map_id] using toLocal)

end
end IGSIII34.Diffusion
