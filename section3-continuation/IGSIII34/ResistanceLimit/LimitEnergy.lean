import IGSIII34.ResistanceLimit.FiniteEnergy
import Mathlib.Topology.Order.MonotoneConvergence

/-!
# Supremum construction for finite trace energies

This is the analytic construction used after exact compatibility has been
established. The finite energies and their domain are defined explicitly;
none of the conclusions below is a structure field. Actual cluster trace
compatibility and the electrical mesh still require a separate instantiation.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace IGSIII34.ResistanceLimit
noncomputable section
open Filter
open scoped Topology

variable {Carrier : Type*} {Edge : ℕ → Type*} [∀ depth, Fintype (Edge depth)]
variable (endpoint : ∀ depth, Edge depth → Carrier × Carrier)
variable (conductance : ∀ depth, Edge depth → ℝ)

def traceEnergy (depth : ℕ) (potential : Carrier → ℝ) : ℝ :=
  finiteEnergy (endpoint depth) (conductance depth) potential

def tracePairing (depth : ℕ) (first second : Carrier → ℝ) : ℝ :=
  finitePairing (endpoint depth) (conductance depth) first second

def limitingEnergy (potential : Carrier → ℝ) : ℝ :=
  ⨆ depth, traceEnergy endpoint conductance depth potential

def energyDomain (nonnegative : ∀ depth edge, 0 ≤ conductance depth edge) : Submodule ℝ (Carrier → ℝ) where
  carrier := {potential | BddAbove (Set.range (fun depth => traceEnergy endpoint conductance depth potential))}
  zero_mem' := by
    refine ⟨0, ?_⟩
    rintro value ⟨depth, rfl⟩
    simp [traceEnergy, finiteEnergy]
  add_mem' := by
    intro first second firstBound secondBound
    obtain ⟨firstUpper, firstUpperBound⟩ := firstBound
    obtain ⟨secondUpper, secondUpperBound⟩ := secondBound
    refine ⟨2 * firstUpper + 2 * secondUpper, ?_⟩
    rintro value ⟨depth, rfl⟩
    have firstBound := firstUpperBound (Set.mem_range_self depth)
    have secondBound := secondUpperBound (Set.mem_range_self depth)
    have bound := finiteEnergy_add_le (endpoint depth) (conductance depth) (nonnegative depth) first second
    change finiteEnergy _ _ (fun vertex => first vertex + second vertex) ≤ _
    change finiteEnergy _ _ first ≤ firstUpper at firstBound
    change finiteEnergy _ _ second ≤ secondUpper at secondBound
    linarith
  smul_mem' := by
    intro scalar potential bound
    obtain ⟨upper, upperBound⟩ := bound
    refine ⟨scalar ^ 2 * upper, ?_⟩
    rintro value ⟨depth, rfl⟩
    change finiteEnergy _ _ (fun vertex => scalar * potential vertex) ≤ _
    rw [finiteEnergy_smul]
    exact mul_le_mul_of_nonneg_left (upperBound (Set.mem_range_self depth)) (sq_nonneg scalar)

variable (nonnegative : ∀ depth edge, 0 ≤ conductance depth edge)

theorem mem_energyDomain_iff (potential : Carrier → ℝ) :
    potential ∈ energyDomain endpoint conductance nonnegative ↔
      BddAbove (Set.range (fun depth => traceEnergy endpoint conductance depth potential)) := Iff.rfl

theorem traceEnergy_le_limitingEnergy {potential : Carrier → ℝ}
    (finite : potential ∈ energyDomain endpoint conductance nonnegative) (depth : ℕ) :
    traceEnergy endpoint conductance depth potential ≤ limitingEnergy endpoint conductance potential :=
  le_ciSup finite depth

theorem limitingEnergy_nonnegative {potential : Carrier → ℝ}
    (finite : potential ∈ energyDomain endpoint conductance nonnegative) :
    0 ≤ limitingEnergy endpoint conductance potential :=
  (finiteEnergy_nonnegative _ _ (nonnegative 0) potential).trans
    (traceEnergy_le_limitingEnergy endpoint conductance nonnegative finite 0)

theorem traceEnergy_tendsto {potential : Carrier → ℝ}
    (finite : potential ∈ energyDomain endpoint conductance nonnegative)
    (monotone : Monotone (fun depth => traceEnergy endpoint conductance depth potential)) :
    Tendsto (fun depth => traceEnergy endpoint conductance depth potential) atTop
      (𝓝 (limitingEnergy endpoint conductance potential)) :=
  tendsto_atTop_ciSup monotone finite

theorem energyDomain_normal_contraction (contraction : ℝ → ℝ)
    (contracts : ∀ first second, |contraction first - contraction second| ≤ |first - second|)
    {potential : Carrier → ℝ} (finite : potential ∈ energyDomain endpoint conductance nonnegative) :
    (fun vertex => contraction (potential vertex)) ∈ energyDomain endpoint conductance nonnegative := by
  obtain ⟨upper, upperBound⟩ := finite
  refine ⟨upper, ?_⟩
  rintro value ⟨depth, rfl⟩
  exact (finiteEnergy_normal_contraction _ _ (nonnegative depth) contraction contracts potential).trans
    (upperBound (Set.mem_range_self depth))

theorem limitingEnergy_normal_contraction (contraction : ℝ → ℝ)
    (contracts : ∀ first second, |contraction first - contraction second| ≤ |first - second|)
    {potential : Carrier → ℝ} (finite : potential ∈ energyDomain endpoint conductance nonnegative) :
    limitingEnergy endpoint conductance (fun vertex => contraction (potential vertex)) ≤
      limitingEnergy endpoint conductance potential := by
  apply ciSup_le
  intro depth
  exact (finiteEnergy_normal_contraction _ _ (nonnegative depth) contraction contracts potential).trans
    (traceEnergy_le_limitingEnergy endpoint conductance nonnegative finite depth)

def limitingPairing (first second : Carrier → ℝ) : ℝ :=
  (limitingEnergy endpoint conductance (fun vertex => first vertex + second vertex) -
    limitingEnergy endpoint conductance first - limitingEnergy endpoint conductance second) / 2

theorem tracePairing_tendsto
    (monotone : ∀ potential, Monotone (fun depth => traceEnergy endpoint conductance depth potential))
    {first second : Carrier → ℝ}
    (firstFinite : first ∈ energyDomain endpoint conductance nonnegative)
    (secondFinite : second ∈ energyDomain endpoint conductance nonnegative) :
    Tendsto (fun depth => tracePairing endpoint conductance depth first second) atTop
      (𝓝 (limitingPairing endpoint conductance first second)) := by
  have sumFinite := (energyDomain endpoint conductance nonnegative).add_mem firstFinite secondFinite
  have convergence := (((traceEnergy_tendsto endpoint conductance nonnegative sumFinite (monotone _)).sub
    (traceEnergy_tendsto endpoint conductance nonnegative firstFinite (monotone _))).sub
    (traceEnergy_tendsto endpoint conductance nonnegative secondFinite (monotone _))).div_const 2
  convert convergence using 1
  · funext depth
    change finitePairing (endpoint depth) (conductance depth) first second =
      (finiteEnergy (endpoint depth) (conductance depth) (fun vertex => first vertex + second vertex) -
        finiteEnergy (endpoint depth) (conductance depth) first - finiteEnergy (endpoint depth) (conductance depth) second) / 2
    have identity := finiteEnergy_add (endpoint depth) (conductance depth) first second
    linarith
  · rfl

theorem limitingPairing_comm
    (monotone : ∀ potential, Monotone (fun depth => traceEnergy endpoint conductance depth potential))
    {first second : Carrier → ℝ}
    (firstFinite : first ∈ energyDomain endpoint conductance nonnegative)
    (secondFinite : second ∈ energyDomain endpoint conductance nonnegative) :
    limitingPairing endpoint conductance first second = limitingPairing endpoint conductance second first := by
  apply tendsto_nhds_unique (tracePairing_tendsto endpoint conductance nonnegative monotone firstFinite secondFinite)
  simpa only [tracePairing, finitePairing_comm] using
    tracePairing_tendsto endpoint conductance nonnegative monotone secondFinite firstFinite

theorem limitingPairing_self
    (monotone : ∀ potential, Monotone (fun depth => traceEnergy endpoint conductance depth potential))
    {potential : Carrier → ℝ} (finite : potential ∈ energyDomain endpoint conductance nonnegative) :
    limitingPairing endpoint conductance potential potential = limitingEnergy endpoint conductance potential := by
  apply tendsto_nhds_unique (tracePairing_tendsto endpoint conductance nonnegative monotone finite finite)
  simpa only [tracePairing, finitePairing_self, traceEnergy] using
    traceEnergy_tendsto endpoint conductance nonnegative finite (monotone _)

theorem limitingPairing_add_left
    (monotone : ∀ potential, Monotone (fun depth => traceEnergy endpoint conductance depth potential))
    {first second third : Carrier → ℝ}
    (firstFinite : first ∈ energyDomain endpoint conductance nonnegative)
    (secondFinite : second ∈ energyDomain endpoint conductance nonnegative)
    (thirdFinite : third ∈ energyDomain endpoint conductance nonnegative) :
    limitingPairing endpoint conductance (fun vertex => first vertex + second vertex) third =
      limitingPairing endpoint conductance first third + limitingPairing endpoint conductance second third := by
  apply tendsto_nhds_unique (tracePairing_tendsto endpoint conductance nonnegative monotone
    ((energyDomain endpoint conductance nonnegative).add_mem firstFinite secondFinite) thirdFinite)
  change Tendsto (fun depth => finitePairing (endpoint depth) (conductance depth)
    (fun vertex => first vertex + second vertex) third) atTop _
  simp_rw [finitePairing_add_left]
  exact
    (tracePairing_tendsto endpoint conductance nonnegative monotone firstFinite thirdFinite).add
      (tracePairing_tendsto endpoint conductance nonnegative monotone secondFinite thirdFinite)

theorem limitingPairing_smul_left
    (monotone : ∀ potential, Monotone (fun depth => traceEnergy endpoint conductance depth potential))
    {first second : Carrier → ℝ}
    (firstFinite : first ∈ energyDomain endpoint conductance nonnegative)
    (secondFinite : second ∈ energyDomain endpoint conductance nonnegative) (scalar : ℝ) :
    limitingPairing endpoint conductance (fun vertex => scalar * first vertex) second =
      scalar * limitingPairing endpoint conductance first second := by
  apply tendsto_nhds_unique (tracePairing_tendsto endpoint conductance nonnegative monotone
    ((energyDomain endpoint conductance nonnegative).smul_mem scalar firstFinite) secondFinite)
  change Tendsto (fun depth => finitePairing (endpoint depth) (conductance depth)
    (fun vertex => scalar * first vertex) second) atTop _
  simp_rw [finitePairing_smul_left]
  exact
    (tracePairing_tendsto endpoint conductance nonnegative monotone firstFinite secondFinite).const_mul scalar

theorem limitingPairing_eq_zero_of_eventually
    (monotone : ∀ potential, Monotone (fun depth => traceEnergy endpoint conductance depth potential))
    {first second : Carrier → ℝ}
    (firstFinite : first ∈ energyDomain endpoint conductance nonnegative)
    (secondFinite : second ∈ energyDomain endpoint conductance nonnegative)
    (zero : ∀ᶠ depth in atTop, tracePairing endpoint conductance depth first second = 0) :
    limitingPairing endpoint conductance first second = 0 :=
  tendsto_nhds_unique (tracePairing_tendsto endpoint conductance nonnegative monotone firstFinite secondFinite)
    (tendsto_const_nhds.congr' (Filter.EventuallyEq.symm zero))

end
end IGSIII34.ResistanceLimit
