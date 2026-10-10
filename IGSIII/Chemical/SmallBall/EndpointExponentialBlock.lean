import IGSIII.Chemical.SmallBall.SignedExponentialConvergence
import IGSIII.Chemical.OrbitDeterministicBounds

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000

namespace IGSIII.Chemical.SmallBall

open Universality MeasureTheory Substitution Filter
open scoped ENNReal Topology

noncomputable section

theorem exists_chemicalOrbit_signed_exponential_block_of_omega_endpoint
    (rule : Rule) (classical : rule.Classical)
    (p : ℝ) (positive : 0 < p) (lessOne : p < 1) (fixedPoint : rule.network.reliability p = p)
    (constant growth : ℝ) (constantPositive : 0 < constant) (growthPositive : 0 < growth)
    (meanBounds : ∀ depth, growth ^ depth ≤ manuscriptDistanceMean rule p depth ∧
      manuscriptDistanceMean rule p depth ≤ constant⁻¹ * growth ^ depth)
    (fixed : Lp ℝ 2 (independentInnovationLaw rule p positive lessOne fixedPoint))
    (fixedPositive : ∀ᵐ marks ∂independentInnovationLaw rule p positive lessOne fixedPoint, 0 < fixed marks)
    (amplitude : ℝ) (amplitudePositive : 0 < amplitude)
    (endpoint : amplitude • fixed ∈ chemicalOmegaSet rule p positive lessOne fixedPoint growth)
    {error ratio : ℝ} (errorPositive : 0 < error) (errorBelow : error < amplitude) (ratioPositive : 0 < ratio) :
    ∃ block : ℕ, ∃ parameter : ℝ, 0 < parameter ∧
      Integrable (fun marks => Real.exp (parameter *
        (chemicalOrbit rule p positive lessOne fixedPoint growth block marks - (amplitude + error) * fixed marks)))
          (independentInnovationLaw rule p positive lessOne fixedPoint) ∧
      (∫ marks, Real.exp (parameter *
        (chemicalOrbit rule p positive lessOne fixedPoint growth block marks - (amplitude + error) * fixed marks))
          ∂independentInnovationLaw rule p positive lessOne fixedPoint) ≤ ratio ∧
      Integrable (fun marks => Real.exp (parameter *
        ((amplitude - error) * fixed marks - chemicalOrbit rule p positive lessOne fixedPoint growth block marks)))
          (independentInnovationLaw rule p positive lessOne fixedPoint) ∧
      (∫ marks, Real.exp (parameter *
        ((amplitude - error) * fixed marks - chemicalOrbit rule p positive lessOne fixedPoint growth block marks))
          ∂independentInnovationLaw rule p positive lessOne fixedPoint) ≤ ratio := by
  obtain ⟨laplaceParameter, laplacePositive, laplaceBounds⟩ := exists_uniform_chemicalOmega_laplace_decay
    rule classical p positive lessOne fixedPoint constant growth growthPositive meanBounds (half_pos ratioPositive)
  let parameter : ℝ := laplaceParameter * amplitude / error
  have parameterPositive : 0 < parameter := div_pos (mul_pos laplacePositive amplitudePositive) errorPositive
  have coefficientEquality : parameter * error = laplaceParameter * amplitude := by
    dsimp [parameter]
    field_simp
  have laplaceBound : (∫⁻ marks, ENNReal.ofReal (Real.exp (-parameter * error * fixed marks))
      ∂independentInnovationLaw rule p positive lessOne fixedPoint) ≤ ENNReal.ofReal (ratio / 2) := by
    calc
      _ = ∫⁻ marks, ENNReal.ofReal (Real.exp (-laplaceParameter * (amplitude • fixed) marks))
          ∂independentInnovationLaw rule p positive lessOne fixedPoint := by
        apply lintegral_congr_ae
        filter_upwards [Lp.coeFn_smul amplitude fixed] with marks equality
        rw [equality, Pi.smul_apply, smul_eq_mul]
        congr 2
        calc
          -parameter * error * fixed marks = -(parameter * error) * fixed marks := by ring
          _ = -(laplaceParameter * amplitude) * fixed marks := by rw [coefficientEquality]
          _ = -laplaceParameter * (amplitude * fixed marks) := by ring
      _ ≤ _ := laplaceBounds (amplitude • fixed) endpoint
  have laplaceLess : (∫ marks, Real.exp (-parameter * error * fixed marks)
      ∂independentInnovationLaw rule p positive lessOne fixedPoint) < ratio := by
    have bound := integral_le_of_lintegral_ofReal_le _ _
      ((Lp.stronglyMeasurable fixed).measurable.const_mul (-parameter * error)).exp.aestronglyMeasurable
      (Eventually.of_forall (fun _ => Real.exp_nonneg _)) (half_pos ratioPositive).le laplaceBound
    linarith
  obtain ⟨subsequence, increasing, convergence⟩ := endpoint.tendsto_subseq
  obtain ⟨sequenceBound, sequenceMoments⟩ := exists_uniform_chemicalOrbit_exponential_moment
    rule classical p positive lessOne fixedPoint constant growth constantPositive growthPositive meanBounds
    (2 * parameter) (by positivity)
  obtain ⟨endpointBound, endpointMoments⟩ := exists_uniform_chemicalOmega_exponential_moment
    rule classical p positive lessOne fixedPoint constant growth constantPositive growthPositive meanBounds
    (2 * parameter) (by positivity)
  have endpointMoment : (∫⁻ marks, ENNReal.ofReal (Real.exp (2 * parameter * amplitude * fixed marks))
      ∂independentInnovationLaw rule p positive lessOne fixedPoint) ≤ ENNReal.ofReal endpointBound := by
    calc
      _ = ∫⁻ marks, ENNReal.ofReal (Real.exp (2 * parameter * (amplitude • fixed) marks))
          ∂independentInnovationLaw rule p positive lessOne fixedPoint := by
        apply lintegral_congr_ae
        filter_upwards [Lp.coeFn_smul amplitude fixed] with marks equality
        rw [equality, Pi.smul_apply, smul_eq_mul, mul_assoc]
      _ ≤ _ := endpointMoments (amplitude • fixed) endpoint
  have sequenceNonnegative (depth : ℕ) : 0 ≤ chemicalOrbit rule p positive lessOne fixedPoint growth (subsequence depth) := by
    apply (Lp.coeFn_nonneg _).mp
    exact (chemicalOrbit_ae_deterministic_bounds rule p positive lessOne fixedPoint growth growthPositive).mono
      (fun marks bounds => (bounds (subsequence depth)).1)
  have fixedNonnegative : 0 ≤ fixed := (Lp.coeFn_nonneg fixed).mp (fixedPositive.mono (fun _ positive => positive.le))
  obtain ⟨integrable, upperConvergence, lowerConvergence⟩ := signed_exponential_integrals_tendsto
    (independentInnovationLaw rule p positive lessOne fixedPoint)
    (chemicalOrbit rule p positive lessOne fixedPoint growth ∘ subsequence) fixed amplitude error parameter
    amplitudePositive errorPositive errorBelow parameterPositive convergence sequenceNonnegative fixedNonnegative
    sequenceBound endpointBound (fun depth => sequenceMoments (subsequence depth)) endpointMoment
  obtain ⟨index, upperLess, lowerLess⟩ :=
    ((upperConvergence.eventually (gt_mem_nhds laplaceLess)).and
      (lowerConvergence.eventually (gt_mem_nhds laplaceLess))).exists
  exact ⟨subsequence index, parameter, parameterPositive, (integrable index).1, upperLess.le,
    (integrable index).2, lowerLess.le⟩

end
end IGSIII.Chemical.SmallBall