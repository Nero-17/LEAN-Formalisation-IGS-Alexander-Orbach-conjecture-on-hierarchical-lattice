import Universality.Percolation.InternalMassLocalLimit
import Universality.Probability.InverseCharacteristicBound
import Universality.Percolation.RenormalisationLimits

namespace Universality.FiniteNetwork
noncomputable section

theorem conditionalInternalMassProbability_nonnegative {vertices edges : ℕ}
    (R : FiniteNetwork vertices edges) (p : ℝ) (hp : 0 ≤ p) (hp' : p ≤ 1)
    (opened sourceSelected targetSelected : Bool) (size : ℕ) :
    0 ≤ R.conditionalInternalMassProbability p opened sourceSelected targetSelected size := by
  apply Finset.sum_nonneg
  intro configuration _
  split_ifs
  · exact R.conditionalCellWeight_nonneg hp hp' _ _
  · exact le_rfl

theorem conditionalInternalMassProbability_le_one {vertices edges : ℕ}
    (R : FiniteNetwork vertices edges) (p : ℝ) (hp : 0 ≤ p) (hp' : p ≤ 1)
    (hpositive : 0 < R.reliability p) (hless : R.reliability p < 1)
    (opened sourceSelected targetSelected : Bool) (size : ℕ) :
    R.conditionalInternalMassProbability p opened sourceSelected targetSelected size ≤ 1 := by
  rw [← R.sum_conditionalCellWeight p hpositive hless opened]
  apply Finset.sum_le_sum
  intro configuration _
  split_ifs
  · exact le_rfl
  · exact R.conditionalCellWeight_nonneg hp hp' _ _

end
end Universality.FiniteNetwork

namespace Universality.Rule
noncomputable section
open FiniteNetwork Matrix MeasureTheory Filter
open scoped Topology
set_option maxHeartbeats 0

theorem Classical.internal_mass_uniform_atom_bound {rule : Rule} (h : rule.Classical)
    (p : ℝ) (hp : 0 < p) (hp' : p < 1) (hfixed : rule.network.reliability p = p) :
    ∃ bound : ℝ, 0 < bound ∧ ∀ (n : ℕ) (state : LiveState) (size : ℕ),
      ((spectralRadius ℂ ((rule.network.massMatrix p).map Complex.ofReal)).toReal) ^ n *
        (rule.generation n).network.conditionalInternalMassProbability p (state == .connected)
          true (state == .both) size ≤ bound := by
  classical
  let radius := (spectralRadius ℂ ((rule.network.massMatrix p).map Complex.ofReal)).toReal
  have hradius : 1 < radius :=
    (rule.network.interior_fixed_point_strictly_unstable p hp hp' hfixed h.scale).trans
      (rule.interior_fixed_point_spectral_dominance p hp hp' hfixed h.massAdmissible.symmetric h.scale).2.1
  have hradius0 : 0 < radius := zero_lt_one.trans hradius
  have hgeneration (n : ℕ) : (rule.generation n).network.reliability p = p := by
    rw [rule.generation_reliability_iterate]
    exact Function.iterate_fixed hfixed (n + 1)
  obtain ⟨limit, hmem, hnonnegative, hmean, huniform, hllt⟩ := h.internal_mass_local_limit p hp hp' hfixed
  have hstateBound (state : LiveState) : ∃ bound : ℝ, 0 < bound ∧ ∀ n size,
      radius ^ n * (rule.generation n).network.conditionalInternalMassProbability p
        (state == .connected) true (state == .both) size ≤ bound := by
    let characteristic := charFun
      ((ConfigurationHistory.infiniteLaw rule p hp hp' hfixed (state == .connected)).map (limit state))
    let fourierBound := (2 * Real.pi)⁻¹ * ∫ t, ‖characteristic t‖
    have hfourierBound : 0 ≤ fourierBound := by dsimp [fourierBound]; positivity
    obtain ⟨threshold, hthreshold⟩ := eventually_atTop.mp ((hllt state).2 1 zero_lt_one)
    refine ⟨radius ^ threshold + fourierBound + 2, by positivity, ?_⟩
    intro n size
    by_cases hn : threshold ≤ n
    · have hnorm := norm_le_norm_sub_add
        ((radius : ℂ) ^ n * ((rule.generation n).network.conditionalInternalMassProbability p
          (state == .connected) true (state == .both) size : ℂ))
        (inverseCharacteristic characteristic ((size : ℝ) / radius ^ n))
      have hlocal := hthreshold n hn size
      have hinverse := inverseCharacteristic_norm_bound characteristic (hllt state).1 ((size : ℝ) / radius ^ n)
      have hprobability := (rule.generation n).network.conditionalInternalMassProbability_nonnegative p hp.le hp'.le
        (state == .connected) true (state == .both) size
      have hnormEqual : ‖(radius : ℂ) ^ n * ((rule.generation n).network.conditionalInternalMassProbability p
          (state == .connected) true (state == .both) size : ℂ)‖ =
          radius ^ n * (rule.generation n).network.conditionalInternalMassProbability p
            (state == .connected) true (state == .both) size := by
        simp [norm_mul, norm_pow, Complex.norm_real, abs_of_nonneg hradius0.le, abs_of_nonneg hprobability]
      rw [hnormEqual] at hnorm
      change _ < 1 at hlocal
      change _ ≤ fourierBound at hinverse
      have hpower : 0 ≤ radius ^ threshold := (pow_pos hradius0 _).le
      linarith
    · have hprobability := (rule.generation n).network.conditionalInternalMassProbability_le_one p hp.le hp'.le
        (by simpa only [hgeneration n] using hp)
        (by simpa only [hgeneration n] using hp')
        (state == .connected) true (state == .both) size
      have hpower : radius ^ n ≤ radius ^ threshold := pow_le_pow_right₀ hradius.le (by omega)
      calc
        _ ≤ radius ^ n := by nlinarith [pow_pos hradius0 n]
        _ ≤ radius ^ threshold := hpower
        _ ≤ _ := by linarith
  choose stateBound hpositive hbound using hstateBound
  refine ⟨∑ state, stateBound state, ?_, ?_⟩
  · exact Finset.sum_pos (fun state _ => hpositive state) Finset.univ_nonempty
  · intro n state size
    exact (hbound state n size).trans
      (Finset.single_le_sum (fun i _ => (hpositive i).le) (Finset.mem_univ state))

end
end Universality.Rule
