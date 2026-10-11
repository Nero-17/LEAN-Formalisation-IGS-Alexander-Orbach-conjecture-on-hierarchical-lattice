import IGSIII34.Forms.AnchoredCore
import IGSIII34.Forms.TraceClosedness
import Mathlib.Topology.MetricSpace.Cauchy

/-! Completeness of the anchored energy norm on a resistance skeleton.
The carrier here is the skeleton, not an arbitrary-function space on its
completion. Continuous extensions to the completion are constructed separately.
-/
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 800000
namespace IGSIII34.Forms
noncomputable section
open IGSIII34.ResistanceLimit Filter
open scoped Topology

variable {Carrier : Type*} [MetricSpace Carrier]
variable {Edge : ℕ → Type*} [∀ depth, Fintype (Edge depth)]
variable (endpoint : ∀ depth, Edge depth → Carrier × Carrier)
variable (conductance : ∀ depth, Edge depth → ℝ)
variable (nonnegative : ∀ depth edge, 0 ≤ conductance depth edge)

def anchoredSquare (anchor : Carrier) (potential : Carrier → ℝ) : ℝ :=
  limitingEnergy endpoint conductance potential + potential anchor ^ 2

theorem anchoredSquare_nonnegative (anchor : Carrier) {potential : Carrier → ℝ}
    (finite : potential ∈ energyDomain endpoint conductance nonnegative) :
    0 ≤ anchoredSquare endpoint conductance anchor potential :=
  add_nonneg (limitingEnergy_nonnegative endpoint conductance nonnegative finite) (sq_nonneg _)

theorem anchoredSquare_evaluation (anchor : Carrier) {potential : Carrier → ℝ}
    (finite : potential ∈ energyDomain endpoint conductance nonnegative)
    (resistanceBound : ∀ first second, (potential first - potential second) ^ 2 ≤
      dist first second * limitingEnergy endpoint conductance potential) (point : Carrier) :
    potential point ^ 2 ≤ 2 * (dist point anchor + 1) *
      anchoredSquare endpoint conductance anchor potential := by
  have energyNonnegative := limitingEnergy_nonnegative endpoint conductance nonnegative finite
  have oscillation := resistanceBound point anchor
  dsimp only [anchoredSquare]
  nlinarith [sq_nonneg (potential point - 2 * potential anchor),
    mul_nonneg (dist_nonneg (x := point) (y := anchor)) (sq_nonneg (potential anchor))]

theorem anchoredSquare_limit_of_uniform_bound
    (anchor : Carrier) (sequence : ℕ → Carrier → ℝ) (limit : Carrier → ℝ) (bound : ℝ)
    (finite : ∀ index, sequence index ∈ energyDomain endpoint conductance nonnegative)
    (convergence : ∀ point, Tendsto (fun index => sequence index point) atTop (𝓝 (limit point)))
    (bounds : ∀ᶠ index in atTop, anchoredSquare endpoint conductance anchor (sequence index) ≤ bound) :
    limit ∈ energyDomain endpoint conductance nonnegative ∧
      anchoredSquare endpoint conductance anchor limit ≤ bound := by
  have traceBounds : ∀ depth, traceEnergy endpoint conductance depth limit + limit anchor ^ 2 ≤ bound := by
    intro depth
    apply le_of_tendsto ((finiteEnergy_tendsto_of_pointwise (endpoint depth)
      (conductance depth) sequence limit convergence).add ((convergence anchor).pow 2))
    filter_upwards [bounds] with index bounded
    have below := traceEnergy_le_limitingEnergy endpoint conductance nonnegative (finite index) depth
    dsimp only [anchoredSquare] at bounded
    change finiteEnergy (endpoint depth) (conductance depth) (sequence index) ≤
      limitingEnergy endpoint conductance (sequence index) at below
    linarith
  have energyBounds : ∀ depth, traceEnergy endpoint conductance depth limit ≤ bound - limit anchor ^ 2 := by
    intro depth
    linarith [traceBounds depth]
  have limitFinite : limit ∈ energyDomain endpoint conductance nonnegative := by
    refine ⟨bound - limit anchor ^ 2, ?_⟩
    rintro value ⟨depth, rfl⟩
    exact energyBounds depth
  refine ⟨limitFinite, ?_⟩
  have limitBound : limitingEnergy endpoint conductance limit ≤ bound - limit anchor ^ 2 :=
    ciSup_le energyBounds
  dsimp only [anchoredSquare]
  linarith

theorem energy_cauchy_pointwise
    (anchor : Carrier) (sequence : ℕ → energyDomain endpoint conductance nonnegative)
    (resistanceBound : ∀ potential ∈ energyDomain endpoint conductance nonnegative,
      ∀ first second, (potential first - potential second) ^ 2 ≤
        dist first second * limitingEnergy endpoint conductance potential)
    (energyCauchy : ∀ epsilon > 0, ∃ threshold : ℕ, ∀ first ≥ threshold, ∀ second ≥ threshold,
      anchoredSquare endpoint conductance anchor
        (fun point => (sequence first).val point - (sequence second).val point) ≤ epsilon)
    (point : Carrier) : CauchySeq (fun index => (sequence index).val point) := by
  apply Metric.cauchySeq_iff.mpr
  intro epsilon positive
  have coefficientPositive : 0 < 2 * (dist point anchor + 1) := by positivity
  obtain ⟨threshold, bounded⟩ := energyCauchy
    (epsilon ^ 2 / (2 * (dist point anchor + 1)) / 2) (by positivity)
  refine ⟨threshold, ?_⟩
  intro first firstAfter second secondAfter
  have finite := (energyDomain endpoint conductance nonnegative).sub_mem
    (sequence first).property (sequence second).property
  have evaluation := anchoredSquare_evaluation endpoint conductance nonnegative anchor finite
    (resistanceBound _ finite) point
  change ((sequence first).val point - (sequence second).val point) ^ 2 ≤
    2 * (dist point anchor + 1) * anchoredSquare endpoint conductance anchor
      (fun point => (sequence first).val point - (sequence second).val point) at evaluation
  have small := bounded first firstAfter second secondAfter
  have multiplied := mul_le_mul_of_nonneg_left small coefficientPositive.le
  have cancel : 2 * (dist point anchor + 1) *
      (epsilon ^ 2 / (2 * (dist point anchor + 1)) / 2) = epsilon ^ 2 / 2 := by
    field_simp
    <;> ring
  rw [cancel] at multiplied
  rw [Real.dist_eq]
  nlinarith [sq_abs ((sequence first).val point - (sequence second).val point),
    abs_nonneg ((sequence first).val point - (sequence second).val point)]

theorem exists_energy_limit_of_cauchy
    (anchor : Carrier) (sequence : ℕ → energyDomain endpoint conductance nonnegative)
    (resistanceBound : ∀ potential ∈ energyDomain endpoint conductance nonnegative,
      ∀ first second, (potential first - potential second) ^ 2 ≤
        dist first second * limitingEnergy endpoint conductance potential)
    (energyCauchy : ∀ epsilon > 0, ∃ threshold : ℕ, ∀ first ≥ threshold, ∀ second ≥ threshold,
      anchoredSquare endpoint conductance anchor
        (fun point => (sequence first).val point - (sequence second).val point) ≤ epsilon) :
    ∃ limit : energyDomain endpoint conductance nonnegative,
      (∀ point, Tendsto (fun index => (sequence index).val point) atTop (𝓝 (limit.val point))) ∧
      ∀ epsilon > 0, ∀ᶠ index in atTop,
        anchoredSquare endpoint conductance anchor
          (fun point => (sequence index).val point - limit.val point) ≤ epsilon := by
  have pointwiseExistence : ∀ point, ∃ value : ℝ,
      Tendsto (fun index => (sequence index).val point) atTop (𝓝 value) := by
    intro point
    exact cauchySeq_tendsto_of_complete
      (energy_cauchy_pointwise endpoint conductance nonnegative anchor sequence resistanceBound energyCauchy point)
  choose limit pointwiseConvergence using pointwiseExistence
  obtain ⟨threshold, bounded⟩ := energyCauchy 1 zero_lt_one
  have differenceFinite : (fun point => limit point - (sequence threshold).val point) ∈
      energyDomain endpoint conductance nonnegative := by
    apply (anchoredSquare_limit_of_uniform_bound endpoint conductance nonnegative anchor
      (fun index point => (sequence index).val point - (sequence threshold).val point)
      (fun point => limit point - (sequence threshold).val point) 1
      (fun index => (energyDomain endpoint conductance nonnegative).sub_mem
        (sequence index).property (sequence threshold).property)
      (fun point => (pointwiseConvergence point).sub_const _)
      ((eventually_ge_atTop threshold).mono (fun index after =>
        bounded index after threshold le_rfl))).1
  have limitFinite : limit ∈ energyDomain endpoint conductance nonnegative := by
    have sumFinite := (energyDomain endpoint conductance nonnegative).add_mem
      differenceFinite (sequence threshold).property
    convert sumFinite using 1
    funext point
    simp
  refine ⟨⟨limit, limitFinite⟩, pointwiseConvergence, ?_⟩
  intro epsilon positive
  obtain ⟨threshold, bounded⟩ := energyCauchy epsilon positive
  filter_upwards [eventually_ge_atTop threshold] with index after
  exact (anchoredSquare_limit_of_uniform_bound endpoint conductance nonnegative anchor
    (fun second point => (sequence index).val point - (sequence second).val point)
    (fun point => (sequence index).val point - limit point) epsilon
    (fun second => (energyDomain endpoint conductance nonnegative).sub_mem
      (sequence index).property (sequence second).property)
    (fun point => tendsto_const_nhds.sub (pointwiseConvergence point))
    ((eventually_ge_atTop threshold).mono (fun second secondAfter =>
      bounded index after second secondAfter))).2

end
end IGSIII34.Forms
