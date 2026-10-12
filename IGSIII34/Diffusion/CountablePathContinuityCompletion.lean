import IGSIII34.Diffusion.CountableTimeLimitsCompletion
import Mathlib.MeasureTheory.OuterMeasure.BorelCantelli
import Mathlib.Analysis.SpecificLimits.Basic

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option backward.isDefEq.respectTransparency false

namespace IGSIII34.Diffusion
noncomputable section
open MeasureTheory Filter Set
open scoped Topology NNReal

variable {Space : Type*} [MetricSpace Space] [CompactSpace Space]
  [MeasurableSpace Space] [BorelSpace Space]

def countableTimeBadModulusCompletion (times : ℕ → ℝ≥0)
    (horizon : ℕ) (duration tolerance : ℝ) : Set (ℕ → Space) :=
  {path | ∃ first last, (times first : ℝ) ≤ horizon ∧ (times last : ℝ) ≤ horizon ∧
    dist (times first) (times last) < duration ∧ tolerance < dist (path first) (path last)}

theorem countableTimeBadModulus_isOpen_completion
    (times : ℕ → ℝ≥0) (horizon : ℕ) (duration tolerance : ℝ) :
    IsOpen (countableTimeBadModulusCompletion (Space := Space) times horizon duration tolerance) := by
  have identity : countableTimeBadModulusCompletion (Space := Space) times horizon duration tolerance =
      ⋃ first : ℕ, ⋃ last : ℕ, ⋃ (_ : (times first : ℝ) ≤ horizon), ⋃ (_ : (times last : ℝ) ≤ horizon),
        ⋃ (_ : dist (times first) (times last) < duration), {path : ℕ → Space | tolerance < dist (path first) (path last)} := by
    ext path
    simp only [countableTimeBadModulusCompletion, mem_setOf_eq, mem_iUnion, exists_prop]
  rw [identity]
  exact isOpen_iUnion fun first => isOpen_iUnion fun last => isOpen_iUnion fun _ =>
    isOpen_iUnion fun _ => isOpen_iUnion fun _ =>
      isOpen_lt continuous_const ((continuous_apply first).dist (continuous_apply last))

theorem countableTimeBadModulus_weak_limit_bound_completion
    (times : ℕ → ℝ≥0) (horizon : ℕ) (duration tolerance error : ℝ) (errorNonnegative : 0 ≤ error)
    (laws : ℕ → ProbabilityMeasure (ℕ → Space)) (limitLaw : ProbabilityMeasure (ℕ → Space))
    (convergence : Tendsto laws atTop (𝓝 limitLaw))
    (bounds : ∀ᶠ depth in atTop, (laws depth : Measure (ℕ → Space)).real
      (countableTimeBadModulusCompletion times horizon duration tolerance) ≤ error) :
    (limitLaw : Measure (ℕ → Space)).real
      (countableTimeBadModulusCompletion times horizon duration tolerance) ≤ error := by
  let bad := countableTimeBadModulusCompletion (Space := Space) times horizon duration tolerance
  have lower := ProbabilityMeasure.le_liminf_measure_open_of_tendsto convergence
    (countableTimeBadModulus_isOpen_completion times horizon duration tolerance)
  have upper : Filter.liminf (fun depth => (laws depth : Measure (ℕ → Space)) bad) atTop ≤ ENNReal.ofReal error := by
    apply Filter.liminf_le_of_le (by isBoundedDefault)
    intro bound eventuallyLower
    have eventuallyUpper : ∀ᶠ depth in atTop, (laws depth : Measure (ℕ → Space)) bad ≤ ENNReal.ofReal error := by
      filter_upwards [bounds] with depth bound
      rw [← ofReal_measureReal]
      exact ENNReal.ofReal_le_ofReal bound
    obtain ⟨depth, below, above⟩ := (eventuallyLower.and eventuallyUpper).exists
    exact below.trans above
  change ((limitLaw : Measure (ℕ → Space)) bad).toReal ≤ error
  exact (by simpa only [ENNReal.toReal_ofReal errorNonnegative] using
    ENNReal.toReal_mono ENNReal.ofReal_ne_top (lower.trans upper))

/-- Summably small modulus-event probabilities imply local uniform
continuity of the actual countable-time sample, with no continuity supplied
as an input. The extension to all real times is a separate construction. -/
theorem countableTimeLaw_ae_local_uniform_continuity_completion
    (times : ℕ → ℝ≥0) (law : ProbabilityMeasure (ℕ → Space))
    (bounds : ∀ horizon : ℕ, ∀ tolerance error : ℝ, 0 < tolerance → 0 < error →
      ∃ duration : ℝ, 0 < duration ∧ (law : Measure (ℕ → Space)).real
        (countableTimeBadModulusCompletion times horizon duration tolerance) ≤ error) :
    ∀ᵐ path ∂(law : Measure (ℕ → Space)), ∀ horizon : ℕ, ∀ tolerance : ℝ, 0 < tolerance →
      ∃ duration : ℝ, 0 < duration ∧ ∀ first last : ℕ,
        (times first : ℝ) ≤ horizon → (times last : ℝ) ≤ horizon →
        dist (times first) (times last) < duration → dist (path first) (path last) < tolerance := by
  classical
  apply ae_all_iff.mpr
  intro horizon
  choose duration durationPositive durationBound using (fun index : ℕ => bounds horizon
    (1 / (index + 1 : ℝ)) ((1 / 2 : ℝ)^index) (by positivity) (by positivity))
  have summable : Summable (fun index : ℕ => (law : Measure (ℕ → Space)).real
      (countableTimeBadModulusCompletion times horizon (duration index) (1 / (index + 1 : ℝ)))) := by
    exact Summable.of_nonneg_of_le (fun _ => measureReal_nonneg) durationBound
      (summable_geometric_of_lt_one (by norm_num : 0 ≤ (1 / 2 : ℝ)) (by norm_num : (1 / 2 : ℝ) < 1))
  have finite : (∑' index : ℕ, (law : Measure (ℕ → Space))
      (countableTimeBadModulusCompletion times horizon (duration index) (1 / (index + 1 : ℝ)))) ≠ ⊤ := by
    have equalities : ∀ index, ENNReal.ofReal ((law : Measure (ℕ → Space)).real
        (countableTimeBadModulusCompletion times horizon (duration index) (1 / (index + 1 : ℝ)))) =
        (law : Measure (ℕ → Space))
          (countableTimeBadModulusCompletion times horizon (duration index) (1 / (index + 1 : ℝ))) :=
      fun _ => ofReal_measureReal
    simpa only [equalities] using summable.tsum_ofReal_ne_top
  filter_upwards [ae_eventually_notMem finite] with path good
  intro tolerance tolerancePositive
  have small : ∀ᶠ index : ℕ in atTop, 1 / (index + 1 : ℝ) < tolerance :=
    tendsto_one_div_add_atTop_nhds_zero_nat.eventually (eventually_lt_nhds tolerancePositive)
  obtain ⟨index, good, small⟩ := (good.and small).exists
  refine ⟨duration index, durationPositive index, ?_⟩
  intro first last firstBefore lastBefore near
  have weakBound : dist (path first) (path last) ≤ 1 / (index + 1 : ℝ) := by
    apply not_lt.mp
    intro far
    exact good ⟨first, last, firstBefore, lastBefore, near, far⟩
  exact weakBound.trans_lt small

/-- The genuine weak limit of countable observations is almost surely
locally uniformly continuous whenever the actual approximating laws have
the proved uniform modulus bounds. This is the portmanteau/BC bridge. -/
theorem countableTimeWeakLimit_ae_local_uniform_continuity_completion
    (times : ℕ → ℝ≥0) (laws : ℕ → ProbabilityMeasure (ℕ → Space))
    (limitLaw : ProbabilityMeasure (ℕ → Space)) (convergence : Tendsto laws atTop (𝓝 limitLaw))
    (bounds : ∀ horizon : ℕ, ∀ tolerance error : ℝ, 0 < tolerance → 0 < error →
      ∃ duration : ℝ, 0 < duration ∧ ∀ᶠ depth in atTop, (laws depth : Measure (ℕ → Space)).real
        (countableTimeBadModulusCompletion times horizon duration tolerance) ≤ error) :
    ∀ᵐ path ∂(limitLaw : Measure (ℕ → Space)), ∀ horizon : ℕ, ∀ tolerance : ℝ, 0 < tolerance →
      ∃ duration : ℝ, 0 < duration ∧ ∀ first last : ℕ,
        (times first : ℝ) ≤ horizon → (times last : ℝ) ≤ horizon →
        dist (times first) (times last) < duration → dist (path first) (path last) < tolerance := by
  apply countableTimeLaw_ae_local_uniform_continuity_completion times limitLaw
  intro horizon tolerance error tolerancePositive errorPositive
  obtain ⟨duration, durationPositive, estimate⟩ := bounds horizon tolerance error tolerancePositive errorPositive
  exact ⟨duration, durationPositive, countableTimeBadModulus_weak_limit_bound_completion
    times horizon duration tolerance error errorPositive.le laws limitLaw convergence estimate⟩

end
end IGSIII34.Diffusion
