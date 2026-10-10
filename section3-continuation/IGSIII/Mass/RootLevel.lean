import IGSIII.Mass.RewardNormalization

set_option autoImplicit false

namespace IGSIII.Mass

open Filter
open scoped Topology

/-- Prepend one root generation and add a fixed boundary reward. The index
shift divides the limiting normalized mass by the growth factor. -/
theorem tendsto_prepend_normalized (sequence : ℕ → ℝ) (initial boundary radius limit : ℝ)
    (radius_gt_one : 1 < radius)
    (convergence : Tendsto (fun n => sequence n / radius ^ n) atTop (𝓝 limit)) :
    Tendsto (fun n => (match n with | 0 => initial | k + 1 => boundary + sequence k) / radius ^ n)
      atTop (𝓝 (limit / radius)) := by
  have boundary_zero : Tendsto (fun n => boundary / radius ^ n) atTop (𝓝 0) := by
    simpa only [mul_zero, div_eq_mul_inv, inv_pow] using
      (tendsto_pow_atTop_nhds_zero_of_abs_lt_one
        (show |radius⁻¹| < 1 by
          rw [abs_of_pos (inv_pos.mpr (zero_lt_one.trans radius_gt_one))]
          exact inv_lt_one_of_one_lt₀ radius_gt_one)).const_mul boundary
  apply (tendsto_add_atTop_iff_nat 1).mp
  have combined := (boundary_zero.add convergence).div_const radius
  simp only [zero_add] at combined
  convert combined using 1
  ext n
  simp only [pow_succ]
  ring

end IGSIII.Mass

namespace Universality.Rule.ConfigurationHistory

open FiniteNetwork Matrix MeasureTheory Filter
open scoped Topology

/-- The live population with III's single-cell generation zero. At generation
`n+1`, it reads the actual graph configuration `generation n` from II. -/
noncomputable def rootLevelPopulation (rule : Rule) (state : LiveState) (values : LiveState → ℝ)
    (n : ℕ) (path : Π k, rule.ConfigurationHistory k) : ℝ :=
  match n with
  | 0 => values state
  | k + 1 => weightedPopulation rule state values k (path k)

/-- Connected selected-vertex count, including its two terminals, in III's
root-level indexing. The subsequent counts are the actual graph counts. -/
noncomputable def rootLevelVertexCount (rule : Rule) (n : ℕ) (path : Π k, rule.ConfigurationHistory k) : ℝ :=
  match n with
  | 0 => 2
  | k + 1 => 2 + vertexMass rule .connected k path

@[simp] theorem rootLevelPopulation_zero (rule : Rule) (state : LiveState) (values : LiveState → ℝ)
    (path : Π k, rule.ConfigurationHistory k) : rootLevelPopulation rule state values 0 path = values state := rfl

@[simp] theorem rootLevelPopulation_succ (rule : Rule) (state : LiveState) (values : LiveState → ℝ)
    (n : ℕ) (path : Π k, rule.ConfigurationHistory k) :
    rootLevelPopulation rule state values (n + 1) path = weightedPopulation rule state values n (path n) := rfl

@[simp] theorem rootLevelVertexCount_succ (rule : Rule) (n : ℕ) (path : Π k, rule.ConfigurationHistory k) :
    rootLevelVertexCount rule (n + 1) path = 2 + vertexMass rule .connected n path := rfl

theorem rootLevelPopulation_tendsto (rule : Rule) (state : LiveState) (values : LiveState → ℝ)
    (radius : ℝ) (radius_gt_one : 1 < radius) (path : Π k, rule.ConfigurationHistory k) (limit : ℝ)
    (convergence : Tendsto (fun n => weightedPopulation rule state values n (path n) / radius ^ n)
      atTop (𝓝 limit)) :
    Tendsto (fun n => rootLevelPopulation rule state values n path / radius ^ n)
      atTop (𝓝 (limit / radius)) := by
  simpa only [rootLevelPopulation, zero_add] using IGSIII.Mass.tendsto_prepend_normalized
    (fun n => weightedPopulation rule state values n (path n)) (values state) 0 radius limit
    radius_gt_one convergence

theorem rootLevelVertexCount_tendsto (rule : Rule) (radius : ℝ) (radius_gt_one : 1 < radius)
    (path : Π k, rule.ConfigurationHistory k) (limit : ℝ)
    (convergence : Tendsto (fun n => vertexMass rule .connected n path / radius ^ n) atTop (𝓝 limit)) :
    Tendsto (fun n => rootLevelVertexCount rule n path / radius ^ n)
      atTop (𝓝 (limit / radius)) :=
  IGSIII.Mass.tendsto_prepend_normalized _ 2 2 radius limit radius_gt_one convergence

end Universality.Rule.ConfigurationHistory
