import IGSIII34.Forms.AnchoredCompleteness
import IGSIII34.Forms.CompletionDomainCompletion20261011
import IGSIII34.Spectral.ComponentResolvent
import Mathlib.MeasureTheory.Integral.BoundedContinuousFunction

/-! Closedness in the energy plus L2 norm, obtained from the proved anchored
completion. The measure is arbitrary probability measure on the resistance
completion. Integrability is an elementary continuous-function obligation,
not a hypothesis asserting closedness of the desired form. -/
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1400000
namespace IGSIII34.Forms
noncomputable section
open IGSIII34.ResistanceLimit Filter MeasureTheory
open scoped Topology

variable {Carrier : Type*} [MetricSpace Carrier]
variable {Edge : ℕ → Type*} [∀ depth, Fintype (Edge depth)]
variable (endpoint : ∀ depth, Edge depth → Carrier × Carrier)
variable (conductance : ∀ depth, Edge depth → ℝ)
variable (nonnegative : ∀ depth edge, 0 ≤ conductance depth edge)
variable (resistanceBound : ∀ potential ∈ energyDomain endpoint conductance nonnegative,
  ∀ first second, (potential first - potential second) ^ 2 ≤
    dist first second * limitingEnergy endpoint conductance potential)

include resistanceBound in
theorem completionExtension_square_le_anchored
    (anchor : Carrier) (diameter : ℝ) (diameterNonnegative : 0 ≤ diameter)
    (diameterBound : ∀ point : UniformSpace.Completion Carrier, dist point anchor ≤ diameter)
    (potential : energyDomain endpoint conductance nonnegative)
    (point : UniformSpace.Completion Carrier) :
    completionExtension endpoint conductance nonnegative potential point ^ 2 ≤
      2 * (diameter + 1) * anchoredSquare endpoint conductance anchor potential.val := by
  have energyNonnegative := limitingEnergy_nonnegative endpoint conductance nonnegative potential.property
  have oscillation := completionExtension_resistance endpoint conductance nonnegative resistanceBound
    potential point (anchor : UniformSpace.Completion Carrier)
  rw [completionExtension_coe endpoint conductance nonnegative resistanceBound] at oscillation
  have oscillationBound := oscillation.trans
    (mul_le_mul_of_nonneg_right (diameterBound point) energyNonnegative)
  dsimp only [anchoredSquare]
  nlinarith [sq_nonneg (completionExtension endpoint conductance nonnegative potential point - 2 * potential.val anchor),
    mul_nonneg diameterNonnegative (sq_nonneg (potential.val anchor))]

section Measure
variable [MeasurableSpace (UniformSpace.Completion Carrier)]
variable (measure : Measure (UniformSpace.Completion Carrier)) [IsProbabilityMeasure measure]

theorem completionExtension_square_integrable
    [BorelSpace (UniformSpace.Completion Carrier)] [CompactSpace (UniformSpace.Completion Carrier)]
    (potential : energyDomain endpoint conductance nonnegative) :
    Integrable (fun point => completionExtension endpoint conductance nonnegative potential point ^ 2) measure := by
  let squared : C(UniformSpace.Completion Carrier, ℝ) :=
    ⟨fun point => completionExtension endpoint conductance nonnegative potential point ^ 2,
      (completionExtension endpoint conductance nonnegative potential).continuous.pow 2⟩
  exact ((BoundedContinuousFunction.mkOfCompact squared).integrable measure).congr
    (Filter.Eventually.of_forall (fun point => by
      change squared point = completionExtension endpoint conductance nonnegative potential point ^ 2
      rfl))

def completionFormSquare (potential : energyDomain endpoint conductance nonnegative) : ℝ :=
  limitingEnergy endpoint conductance potential.val +
    ∫ point, completionExtension endpoint conductance nonnegative potential point ^ 2 ∂measure

theorem completionFormSquare_nonnegative (potential : energyDomain endpoint conductance nonnegative) :
    0 ≤ completionFormSquare endpoint conductance nonnegative measure potential :=
  add_nonneg (limitingEnergy_nonnegative endpoint conductance nonnegative potential.property)
    (integral_nonneg (fun point => sq_nonneg _))

include resistanceBound in
theorem anchoredSquare_le_completionFormSquare
    (anchor : Carrier) (diameter : ℝ) (diameterNonnegative : 0 ≤ diameter)
    (diameterBound : ∀ point : UniformSpace.Completion Carrier,
      dist (anchor : UniformSpace.Completion Carrier) point ≤ diameter)
    (potential : energyDomain endpoint conductance nonnegative)
    (integrable : Integrable (fun point => completionExtension endpoint conductance nonnegative potential point ^ 2) measure) :
    anchoredSquare endpoint conductance anchor potential.val ≤
      (2 * diameter + 3) * completionFormSquare endpoint conductance nonnegative measure potential := by
  have energyNonnegative := limitingEnergy_nonnegative endpoint conductance nonnegative potential.property
  have squareNonnegative : 0 ≤ ∫ point, completionExtension endpoint conductance nonnegative potential point ^ 2 ∂measure :=
    integral_nonneg (fun point => sq_nonneg _)
  have evaluated := IGSIII34.Spectral.point_evaluation_le_of_resistance_inequality
    measure (completionExtension endpoint conductance nonnegative potential)
    (anchor : UniformSpace.Completion Carrier) diameter (limitingEnergy endpoint conductance potential.val)
    (by simp [measureReal_def]) integrable (Filter.Eventually.of_forall (fun point =>
      (completionExtension_resistance endpoint conductance nonnegative resistanceBound potential anchor point).trans
        (mul_le_mul_of_nonneg_right (diameterBound point) energyNonnegative)))
  rw [completionExtension_coe endpoint conductance nonnegative resistanceBound] at evaluated
  have mass : measure.real Set.univ = 1 := by simp [measureReal_def]
  rw [mass] at evaluated
  dsimp only [anchoredSquare, completionFormSquare]
  norm_num only [div_one] at evaluated
  nlinarith

include resistanceBound in
theorem exists_energy_limit_of_form_cauchy
    (anchor : Carrier) (diameter : ℝ) (diameterNonnegative : 0 ≤ diameter)
    (diameterBound : ∀ point : UniformSpace.Completion Carrier,
      dist (anchor : UniformSpace.Completion Carrier) point ≤ diameter)
    (sequence : ℕ → energyDomain endpoint conductance nonnegative)
    (squareIntegrable : ∀ first second,
      Integrable (fun point => completionExtension endpoint conductance nonnegative
        (sequence first - sequence second) point ^ 2) measure)
    (formCauchy : ∀ epsilon > 0, ∃ threshold : ℕ, ∀ first ≥ threshold, ∀ second ≥ threshold,
      completionFormSquare endpoint conductance nonnegative measure (sequence first - sequence second) ≤ epsilon) :
    ∃ limit : energyDomain endpoint conductance nonnegative,
      (∀ point, Tendsto (fun index => (sequence index).val point) atTop (𝓝 (limit.val point))) ∧
      ∀ epsilon > 0, ∀ᶠ index in atTop,
        anchoredSquare endpoint conductance anchor
          (fun point => (sequence index).val point - limit.val point) ≤ epsilon := by
  apply exists_energy_limit_of_cauchy endpoint conductance nonnegative anchor sequence resistanceBound
  intro epsilon positive
  obtain ⟨threshold, bounds⟩ := formCauchy (epsilon / (2 * diameter + 3)) (by positivity)
  refine ⟨threshold, ?_⟩
  intro first firstAfter second secondAfter
  have below := anchoredSquare_le_completionFormSquare endpoint conductance nonnegative resistanceBound
    measure anchor diameter diameterNonnegative diameterBound (sequence first - sequence second)
    (squareIntegrable first second)
  have multiplied := mul_le_mul_of_nonneg_left (bounds first firstAfter second secondAfter)
    (show 0 ≤ 2 * diameter + 3 by positivity)
  rw [mul_div_cancel₀ _ (show 2 * diameter + 3 ≠ 0 by positivity)] at multiplied
  exact below.trans multiplied

include resistanceBound in
theorem completionFormSquare_le_anchoredSquare
    [BorelSpace (UniformSpace.Completion Carrier)] [CompactSpace (UniformSpace.Completion Carrier)]
    (anchor : Carrier) (diameter : ℝ) (diameterNonnegative : 0 ≤ diameter)
    (diameterBound : ∀ point : UniformSpace.Completion Carrier,
      dist point (anchor : UniformSpace.Completion Carrier) ≤ diameter)
    (potential : energyDomain endpoint conductance nonnegative) :
    completionFormSquare endpoint conductance nonnegative measure potential ≤
      (2 * diameter + 3) * anchoredSquare endpoint conductance anchor potential.val := by
  have integrated := integral_mono
    (completionExtension_square_integrable endpoint conductance nonnegative measure potential)
    (integrable_const (2 * (diameter + 1) * anchoredSquare endpoint conductance anchor potential.val))
    (fun point => completionExtension_square_le_anchored endpoint conductance nonnegative resistanceBound
      anchor diameter diameterNonnegative diameterBound potential point)
  rw [integral_const, smul_eq_mul] at integrated
  have mass : measure.real Set.univ = 1 := by simp [measureReal_def]
  rw [mass, one_mul] at integrated
  have below : limitingEnergy endpoint conductance potential.val ≤
      anchoredSquare endpoint conductance anchor potential.val := by
    dsimp only [anchoredSquare]
    exact le_add_of_nonneg_right (sq_nonneg _)
  dsimp only [completionFormSquare]
  nlinarith

include resistanceBound in
theorem exists_completion_form_limit_of_cauchy
    [BorelSpace (UniformSpace.Completion Carrier)] [CompactSpace (UniformSpace.Completion Carrier)]
    (anchor : Carrier) (diameter : ℝ) (diameterNonnegative : 0 ≤ diameter)
    (diameterBound : ∀ point : UniformSpace.Completion Carrier,
      dist (anchor : UniformSpace.Completion Carrier) point ≤ diameter)
    (sequence : ℕ → energyDomain endpoint conductance nonnegative)
    (formCauchy : ∀ epsilon > 0, ∃ threshold : ℕ, ∀ first ≥ threshold, ∀ second ≥ threshold,
      completionFormSquare endpoint conductance nonnegative measure (sequence first - sequence second) ≤ epsilon) :
    ∃ limit : energyDomain endpoint conductance nonnegative,
      (∀ point, Tendsto (fun index => (sequence index).val point) atTop (𝓝 (limit.val point))) ∧
      ∀ epsilon > 0, ∀ᶠ index in atTop,
        completionFormSquare endpoint conductance nonnegative measure (sequence index - limit) ≤ epsilon := by
  obtain ⟨limit, pointwise, convergence⟩ := exists_energy_limit_of_form_cauchy endpoint conductance nonnegative
    resistanceBound measure anchor diameter diameterNonnegative diameterBound sequence
    (fun first second => completionExtension_square_integrable endpoint conductance nonnegative measure
      (sequence first - sequence second)) formCauchy
  refine ⟨limit, pointwise, ?_⟩
  intro epsilon positive
  filter_upwards [convergence (epsilon / (2 * diameter + 3)) (by positivity)] with index small
  have below := completionFormSquare_le_anchoredSquare endpoint conductance nonnegative resistanceBound
    measure anchor diameter diameterNonnegative (fun point => by simpa only [dist_comm] using diameterBound point)
    (sequence index - limit)
  have multiplied := mul_le_mul_of_nonneg_left small (show 0 ≤ 2 * diameter + 3 by positivity)
  rw [mul_div_cancel₀ _ (show 2 * diameter + 3 ≠ 0 by positivity)] at multiplied
  exact below.trans multiplied

end Measure
end
end IGSIII34.Forms
