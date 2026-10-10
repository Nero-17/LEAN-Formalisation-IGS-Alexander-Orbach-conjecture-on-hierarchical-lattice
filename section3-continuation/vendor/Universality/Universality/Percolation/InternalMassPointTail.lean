import Universality.Percolation.InternalMassPointPowerRecursion
import Universality.Percolation.InternalMassAtomBound
import Universality.Probability.PolynomialPointTail
import Universality.Percolation.VertexMomentGrowth

namespace Universality.Rule
noncomputable section
open FiniteNetwork Matrix

/-- The actual conditional internal mass has all integer-order spatial point
bounds, uniformly in generation and live state. -/
theorem Classical.internal_mass_polynomial_point_tail {rule : Rule} (h : rule.Classical)
    (p : ℝ) (hp : 0 < p) (hp' : p < 1) (hfixed : rule.network.reliability p = p)
    (order : ℕ) :
    ∃ bound : ℝ, 0 < bound ∧ ∀ (n : ℕ) (state : LiveState) (size : ℕ),
      (rule.generation n).network.conditionalInternalMassProbability p (state == .connected)
        true (state == .both) size ≤
      bound / ((spectralRadius ℂ ((rule.network.massMatrix p).map Complex.ofReal)).toReal) ^ n /
        (1 + (size : ℝ) / ((spectralRadius ℂ ((rule.network.massMatrix p).map Complex.ofReal)).toReal) ^ n) ^ order := by
  let radius := (spectralRadius ℂ ((rule.network.massMatrix p).map Complex.ofReal)).toReal
  have hradius : 1 < radius :=
    (rule.network.interior_fixed_point_strictly_unstable p hp hp' hfixed h.scale).trans
      (rule.interior_fixed_point_spectral_dominance p hp hp' hfixed h.massAdmissible.symmetric h.scale).2.1
  have hradius0 : 0 < radius := zero_lt_one.trans hradius
  obtain ⟨atomBound, hatomPositive, hatom⟩ := h.internal_mass_uniform_atom_bound p hp hp' hfixed
  obtain ⟨momentBound, hmomentPositive, hmoment⟩ := h.internal_vertex_moment_bounds p hp hp' hfixed order
  let powerBound := momentBound + 2 ^ (order + 1) * atomBound * momentBound * radius
  have hpowerPositive : 0 < powerBound := by dsimp [powerBound]; positivity
  have hnormalized (n : ℕ) (state : LiveState) (size : ℕ) :
      radius ^ n * (rule.generation n).network.conditionalInternalMassProbability p
        (state == .connected) true (state == .both) size * ((size : ℝ) / radius ^ n) ^ order ≤ powerBound := by
    cases n with
    | zero =>
      have hfinite := finite_atom_power_le_moment
        ((rule.generation 0).network.conditionalCellWeight p (state == .connected))
        ((rule.generation 0).network.internalSelectedMass true (state == .both))
        (fun configuration => (rule.generation 0).network.conditionalCellWeight_nonneg hp.le hp'.le _ _) order size
      have hzero : (size : ℝ) ^ order * (rule.generation 0).network.conditionalInternalMassProbability p
          (state == .connected) true (state == .both) size ≤
          (rule.generation 0).network.conditionalVertexMoment p state order := hfinite
      have hbound := hmoment 0 state
      simp only [Nat.mul_zero, pow_zero, mul_one] at hbound
      simp only [pow_zero, one_mul, div_one]
      dsimp only [powerBound]
      have hremaining : 0 ≤ 2 ^ (order + 1) * atomBound * momentBound * radius := by positivity
      nlinarith
    | succ n =>
      have hchild (child : LiveState) (target : ℕ) :
          (rule.generation n).network.conditionalInternalMassProbability p (child == .connected)
            true (child == .both) target ≤ atomBound / radius ^ n := by
        apply (le_div_iff₀ (pow_pos hradius0 n)).mpr
        simpa only [mul_comm] using hatom n child target
      have hrecursion := h.internal_mass_point_power_recursion p hp hp' hfixed n
        (atomBound / radius ^ n) (by positivity) hchild state order size
      have htotal : (size : ℝ) ^ order * (rule.generation (n + 1)).network.conditionalInternalMassProbability p
          (state == .connected) true (state == .both) size ≤
          2 ^ (order + 1) * (atomBound / radius ^ n) *
            (momentBound * radius ^ (order * (n + 1))) :=
        hrecursion.trans (mul_le_mul_of_nonneg_left (hmoment (n + 1) state) (by positivity))
      have hscale : 0 < radius ^ (n + 1) := pow_pos hradius0 _
      calc
        _ = (radius ^ (n + 1) / (radius ^ (n + 1)) ^ order) *
            ((size : ℝ) ^ order * (rule.generation (n + 1)).network.conditionalInternalMassProbability p
              (state == .connected) true (state == .both) size) := by rw [div_pow]; ring
        _ ≤ (radius ^ (n + 1) / (radius ^ (n + 1)) ^ order) *
            (2 ^ (order + 1) * (atomBound / radius ^ n) *
              (momentBound * radius ^ (order * (n + 1)))) :=
          mul_le_mul_of_nonneg_left htotal (by positivity)
        _ = 2 ^ (order + 1) * atomBound * momentBound * radius := by
          rw [Nat.mul_comm order (n + 1), pow_mul]
          field_simp [hradius0.ne']
          rw [pow_succ]
        _ ≤ powerBound := by dsimp [powerBound]; linarith
  refine ⟨2 ^ (order - 1) * (atomBound + powerBound), by positivity, ?_⟩
  intro n state size
  exact polynomial_point_tail_of_two_bounds (radius ^ n) size
    ((rule.generation n).network.conditionalInternalMassProbability p (state == .connected) true (state == .both) size)
    atomBound powerBound (pow_pos hradius0 n) (Nat.cast_nonneg _)
    ((rule.generation n).network.conditionalInternalMassProbability_nonnegative p hp.le hp'.le _ _ _ _)
    order (hatom n state size) (hnormalized n state size)

end
end Universality.Rule
