import IGSIII.Chemical.SmallBall.FactorialMoments
import IGSIII.Chemical.SmallBall.PathLaplace
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Analysis.SpecificLimits.Basic

/-! Factorial bounds give a uniform exponential moment near zero.  A separate
recursion extends such a bound to all finite positive parameters. -/

set_option autoImplicit false

namespace IGSIII.Chemical.SmallBall

open Filter Set
open scoped BigOperators Topology

noncomputable section

variable {Outcome : Type*} [Fintype Outcome]

theorem finite_exponential_moment_bound_of_factorial (weight value : Outcome → ℝ)
    {constant parameter : ℝ} (constantNonnegative : 0 ≤ constant)
    (parameterNonnegative : 0 ≤ parameter) (parameterSmall : constant * parameter < 1)
    (momentBound : ∀ power : ℕ, (∑ outcome, weight outcome * value outcome ^ power) ≤
      constant ^ power * (power.factorial : ℝ)) :
    (∑ outcome, weight outcome * Real.exp (parameter * value outcome)) ≤
      (1 - constant * parameter)⁻¹ := by
  have expansion (outcome : Outcome) :
      HasSum (fun power : ℕ => weight outcome *
        ((parameter * value outcome) ^ power / (power.factorial : ℝ)))
        (weight outcome * Real.exp (parameter * value outcome)) := by
    simpa only [← Real.exp_eq_exp_ℝ] using
      (NormedSpace.expSeries_div_hasSum_exp (parameter * value outcome)).mul_left (weight outcome)
  have combined : HasSum (fun power : ℕ => ∑ outcome, weight outcome *
      ((parameter * value outcome) ^ power / (power.factorial : ℝ)))
      (∑ outcome, weight outcome * Real.exp (parameter * value outcome)) :=
    hasSum_sum (fun outcome _ => expansion outcome)
  have termBound (power : ℕ) :
      (∑ outcome, weight outcome *
        ((parameter * value outcome) ^ power / (power.factorial : ℝ))) ≤
        (constant * parameter) ^ power := by
    have rearrange (outcome : Outcome) :
        weight outcome * ((parameter * value outcome) ^ power / (power.factorial : ℝ)) =
        (parameter ^ power / (power.factorial : ℝ)) * (weight outcome * value outcome ^ power) := by
      rw [mul_pow]
      ring
    simp_rw [rearrange]
    rw [← Finset.mul_sum]
    calc
      _ ≤ (parameter ^ power / (power.factorial : ℝ)) *
          (constant ^ power * (power.factorial : ℝ)) :=
        mul_le_mul_of_nonneg_left (momentBound power) (by positivity)
      _ = _ := by
        have factorialNonzero : (power.factorial : ℝ) ≠ 0 := by positivity
        rw [mul_pow]
        field_simp
  have geometric := summable_geometric_of_lt_one
    (mul_nonneg constantNonnegative parameterNonnegative) parameterSmall
  calc
    _ ≤ ∑' power : ℕ, (constant * parameter) ^ power :=
      hasSum_le termBound combined geometric.hasSum
    _ = _ := tsum_geometric_of_lt_one
      (mul_nonneg constantNonnegative parameterNonnegative) parameterSmall

/-- The scalar bootstrap needed after the selected-path exponential estimate.
The finite initial levels are controlled by their actual finite exponential
moments, represented by the separate initial bound. -/
theorem uniform_exponential_bound_at_scaled_parameter
    {moment : ℕ → ℝ → ℝ} {base parameter bound : ℝ} {length : ℕ}
    (parameterNonnegative : 0 ≤ parameter)
    (atParameter : ∀ depth, moment depth parameter ≤ bound)
    (initial : moment 0 (base * parameter) ≤ bound ^ length)
    (nonnegative : ∀ depth argument, 0 ≤ moment depth argument)
    (step : ∀ depth argument, 0 ≤ argument →
      moment (depth + 1) (base * argument) ≤ (moment depth argument) ^ length) :
    ∀ depth, moment depth (base * parameter) ≤ bound ^ length := by
  intro depth
  cases depth with
  | zero => exact initial
  | succ depth =>
      exact (step depth parameter parameterNonnegative).trans
        (pow_le_pow_left₀ (nonnegative depth parameter) (atParameter depth) length)

theorem exists_uniform_exponential_bound_at_every_parameter
    {moment : ℕ → ℝ → ℝ} {base initialParameter initialBound : ℝ} {length : ℕ}
    (baseAboveOne : 1 < base) (initialParameterPositive : 0 < initialParameter)
    (atInitialParameter : ∀ depth, moment depth initialParameter ≤ initialBound)
    (nonnegative : ∀ depth argument, 0 ≤ moment depth argument)
    (monotone : ∀ depth, MonotoneOn (moment depth) (Ici 0))
    (step : ∀ depth argument, 0 ≤ argument →
      moment (depth + 1) (base * argument) ≤ (moment depth argument) ^ length) :
    ∀ parameter : ℝ, 0 ≤ parameter → ∃ bound : ℝ, ∀ depth, moment depth parameter ≤ bound := by
  have atScales : ∀ level : ℕ, ∃ bound : ℝ, 1 ≤ bound ∧
      ∀ depth, moment depth (base ^ level * initialParameter) ≤ bound := by
    intro level
    induction level with
    | zero =>
        refine ⟨max 1 initialBound, le_max_left _ _, ?_⟩
        intro depth
        simpa only [pow_zero, one_mul] using (atInitialParameter depth).trans (le_max_right _ _)
    | succ level inductionHypothesis =>
        obtain ⟨bound, _, atParameter⟩ := inductionHypothesis
        refine ⟨max 1 (max (bound ^ length)
          (moment 0 (base ^ (level + 1) * initialParameter))), le_max_left _ _, ?_⟩
        intro depth
        cases depth with
        | zero => exact (le_max_right _ _).trans (le_max_right _ _)
        | succ depth =>
            have parameterNonnegative : 0 ≤ base ^ level * initialParameter := by positivity
            have bound := (step depth _ parameterNonnegative).trans
              (pow_le_pow_left₀ (nonnegative depth _) (atParameter depth) length)
            have parameterIdentity : base * (base ^ level * initialParameter) =
                base ^ (level + 1) * initialParameter := by rw [pow_succ]; ring
            rw [parameterIdentity] at bound
            exact bound.trans ((le_max_left _ _).trans (le_max_right _ _))
  intro parameter parameterNonnegative
  obtain ⟨level, exceeds⟩ := pow_unbounded_of_one_lt (parameter / initialParameter) baseAboveOne
  have parameterComparison : parameter ≤ base ^ level * initialParameter :=
    (div_le_iff₀ initialParameterPositive).mp exceeds.le
  obtain ⟨bound, _, atScale⟩ := atScales level
  refine ⟨bound, fun depth => ?_⟩
  exact (monotone depth parameterNonnegative
    (by change 0 ≤ base ^ level * initialParameter; positivity) parameterComparison).trans (atScale depth)

theorem finite_exponential_moment_monotone (weight value : Outcome → ℝ)
    (weightNonnegative : ∀ outcome, 0 ≤ weight outcome)
    (valueNonnegative : ∀ outcome, 0 ≤ value outcome) :
    Monotone (fun parameter => ∑ outcome, weight outcome * Real.exp (parameter * value outcome)) := by
  intro first second ordered
  apply Finset.sum_le_sum
  intro outcome _
  exact mul_le_mul_of_nonneg_left
    (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right ordered (valueNonnegative outcome)))
    (weightNonnegative outcome)

theorem selected_path_exponential_moment_bound {Root Edge : Type*}
    [Fintype Root] [Fintype Edge] [DecidableEq Edge]
    (rootWeight : Root → ℝ) (family : Root → PathFamily Edge)
    (selected : Root → Finset Edge) (selectedMember : ∀ root, selected root ∈ (family root).paths)
    (weight value : Root → Edge → Outcome → ℝ)
    (rootNonnegative : ∀ root, 0 ≤ rootWeight root) (rootNormalized : ∑ root, rootWeight root = 1)
    (weightNonnegative : ∀ root edge outcome, 0 ≤ weight root edge outcome)
    (normalized : ∀ root edge, ∑ outcome, weight root edge outcome = 1)
    {parameter bound : ℝ} {length : ℕ} (parameterNonnegative : 0 ≤ parameter)
    (boundAtLeastOne : 1 ≤ bound) (lengthBound : ∀ root, (selected root).card ≤ length)
    (exponentialBound : ∀ root edge, edge ∈ selected root →
      (∑ outcome, weight root edge outcome * Real.exp (parameter * value root edge outcome)) ≤ bound) :
    (∑ root, rootWeight root * ∑ outcome : Edge → Outcome,
      (∏ edge, weight root edge (outcome edge)) *
        Real.exp (parameter * (family root).shortest (fun edge => value root edge (outcome edge)))) ≤
      bound ^ length := by
  have rootBound (root : Root) :
      (∑ outcome : Edge → Outcome, (∏ edge, weight root edge (outcome edge)) *
        Real.exp (parameter * (family root).shortest (fun edge => value root edge (outcome edge)))) ≤
        bound ^ length := by
    have exponentialIdentity (outcome : Edge → Outcome) :
        parameter * (∑ edge ∈ selected root, value root edge (outcome edge)) =
          ∑ edge ∈ selected root, parameter * value root edge (outcome edge) := by
      rw [Finset.mul_sum]
    calc
      _ ≤ ∑ outcome : Edge → Outcome, (∏ edge, weight root edge (outcome edge)) *
          Real.exp (parameter * (∑ edge ∈ selected root, value root edge (outcome edge))) := by
        apply Finset.sum_le_sum
        intro outcome _
        exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr
          (mul_le_mul_of_nonneg_left
            ((family root).shortest_le_pathCost _ (selectedMember root)) parameterNonnegative))
          (Finset.prod_nonneg (fun edge _ => weightNonnegative root edge (outcome edge)))
      _ = ∏ edge ∈ selected root, ∑ outcome,
          weight root edge outcome * Real.exp (parameter * value root edge outcome) := by
        simp_rw [exponentialIdentity]
        exact finite_product_path_exponential (weight root)
          (fun edge outcome => parameter * value root edge outcome) (normalized root) (selected root)
      _ ≤ bound ^ (selected root).card := by
        simpa only [Finset.prod_const] using Finset.prod_le_prod
          (fun edge _ => Finset.sum_nonneg (fun outcome _ =>
            mul_nonneg (weightNonnegative root edge outcome) (Real.exp_nonneg _))) (exponentialBound root)
      _ ≤ bound ^ length := pow_le_pow_right₀ boundAtLeastOne (lengthBound root)
  calc
    _ ≤ ∑ root, rootWeight root * bound ^ length := Finset.sum_le_sum
      (fun root _ => mul_le_mul_of_nonneg_left (rootBound root) (rootNonnegative root))
    _ = _ := by rw [← Finset.sum_mul, rootNormalized, one_mul]

theorem selected_path_normalized_exponential_moment_bound {Root Edge : Type*}
    [Fintype Root] [Fintype Edge] [DecidableEq Edge]
    (rootWeight : Root → ℝ) (family : Root → PathFamily Edge)
    (selected : Root → Finset Edge) (selectedMember : ∀ root, selected root ∈ (family root).paths)
    (weight value : Root → Edge → Outcome → ℝ)
    (rootNonnegative : ∀ root, 0 ≤ rootWeight root) (rootNormalized : ∑ root, rootWeight root = 1)
    (weightNonnegative : ∀ root edge outcome, 0 ≤ weight root edge outcome)
    (valueNonnegative : ∀ root edge outcome, 0 ≤ value root edge outcome)
    (normalized : ∀ root edge, ∑ outcome, weight root edge outcome = 1)
    {base normalizer parameter bound : ℝ} {length : ℕ}
    (normalizerPositive : 0 < normalizer) (baseBound : base ≤ normalizer)
    (parameterNonnegative : 0 ≤ parameter) (boundAtLeastOne : 1 ≤ bound)
    (lengthBound : ∀ root, (selected root).card ≤ length)
    (exponentialBound : ∀ root edge, edge ∈ selected root →
      (∑ outcome, weight root edge outcome * Real.exp (parameter * value root edge outcome)) ≤ bound) :
    (∑ root, rootWeight root * ∑ outcome : Edge → Outcome,
      (∏ edge, weight root edge (outcome edge)) *
        Real.exp ((base * parameter) *
          ((family root).shortest (fun edge => value root edge (outcome edge)) / normalizer))) ≤
      bound ^ length := by
  have ratioBound : base / normalizer ≤ 1 := (div_le_one normalizerPositive).mpr baseBound
  have exponentBound (root : Root) (outcome : Edge → Outcome) :
      (base * parameter) *
          ((family root).shortest (fun edge => value root edge (outcome edge)) / normalizer) ≤
        parameter * (family root).shortest (fun edge => value root edge (outcome edge)) := by
    have costNonnegative := (family root).shortest_nonneg
      (fun edge => valueNonnegative root edge (outcome edge))
    have comparison := mul_le_mul_of_nonneg_right ratioBound
      (mul_nonneg parameterNonnegative costNonnegative)
    calc
      _ = (base / normalizer) *
          (parameter * (family root).shortest (fun edge => value root edge (outcome edge))) := by ring
      _ ≤ _ := by simpa only [one_mul] using comparison
  calc
    _ ≤ ∑ root, rootWeight root * ∑ outcome : Edge → Outcome,
        (∏ edge, weight root edge (outcome edge)) *
          Real.exp (parameter * (family root).shortest (fun edge => value root edge (outcome edge))) := by
      apply Finset.sum_le_sum
      intro root _
      apply mul_le_mul_of_nonneg_left _ (rootNonnegative root)
      apply Finset.sum_le_sum
      intro outcome _
      exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (exponentBound root outcome))
        (Finset.prod_nonneg (fun edge _ => weightNonnegative root edge (outcome edge)))
    _ ≤ _ := selected_path_exponential_moment_bound rootWeight family selected selectedMember
      weight value rootNonnegative rootNormalized weightNonnegative normalized
      parameterNonnegative boundAtLeastOne lengthBound exponentialBound

end
end IGSIII.Chemical.SmallBall
