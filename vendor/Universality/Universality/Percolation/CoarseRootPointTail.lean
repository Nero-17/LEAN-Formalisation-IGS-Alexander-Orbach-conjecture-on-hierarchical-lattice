import Universality.Percolation.CoarseRootMoments
import Universality.Percolation.CoarseRootPointRecursion
import Universality.Percolation.BirthInteriorPointBounds
import Universality.Percolation.InternalMassAtomBound
import Universality.Probability.PolynomialPointTail

namespace Universality.Rule
noncomputable section
open FiniteNetwork Matrix
set_option maxHeartbeats 0

/-- Actual fine-cluster masses rooted at old interior vertices have uniform spatial point tails. -/
theorem Classical.coarse_root_polynomial_point_tail {rule : Rule} (h : rule.Classical)
    (p : ℝ) (hp : 0 < p) (hp' : p < 1) (hfixed : rule.network.reliability p = p)
    (order : ℕ) (horder : 1 ≤ order) :
    ∃ bound : ℝ, 0 < bound ∧ ∀ (n : ℕ) (root : rule.network.InteriorVertex) (size : ℕ),
      rule.network.coarseRootMassObservable (rule.generation n).network p root.val
        (fun mass => if mass = size then 1 else 0) ≤
      bound / ((spectralRadius ℂ ((rule.network.massMatrix p).map Complex.ofReal)).toReal) ^ n /
        (1 + (size : ℝ) / ((spectralRadius ℂ ((rule.network.massMatrix p).map Complex.ofReal)).toReal) ^ n) ^ order := by
  let radius := (spectralRadius ℂ ((rule.network.massMatrix p).map Complex.ofReal)).toReal
  have hradius : 1 < radius :=
    (rule.network.interior_fixed_point_strictly_unstable p hp hp' hfixed h.scale).trans
      (rule.interior_fixed_point_spectral_dominance p hp hp' hfixed h.massAdmissible.symmetric h.scale).2.1
  have hradius0 : 0 < radius := zero_lt_one.trans hradius
  obtain ⟨atomBound, hatomPositive, hatom⟩ := h.internal_mass_uniform_atom_bound p hp hp' hfixed
  obtain ⟨momentBound, hmomentPositive, hmoment⟩ := h.internal_boundary_moment_bounds p hp hp' hfixed order
  let rootMomentBound := 1 + ((rule.edges : ℝ) + 1) ^ (order - 1) *
    ((rule.vertices : ℝ) ^ order + (rule.edges : ℝ) * momentBound)
  have hrootMomentPositive : 0 < rootMomentBound := by dsimp [rootMomentBound]; positivity
  have hrootMoment (n : ℕ) (root : rule.network.InteriorVertex) :
      rule.network.coarseRootMassObservable (rule.generation n).network p root.val
        (fun mass => (mass : ℝ) ^ order) ≤ rootMomentBound * radius ^ (order * n) := by
    have hbase := rule.network.coarseRootMassObservable_power_le_boundary_moment
      (rule.generation n).network hp.le hp'.le root.val order horder
    have hupper := hmoment n
    have hscale : 1 ≤ radius ^ (order * n) := one_le_pow₀ hradius.le
    have hv : 0 ≤ (rule.vertices : ℝ) ^ order := by positivity
    have he : 0 ≤ (rule.edges : ℝ) := Nat.cast_nonneg _
    have hc : 0 ≤ ((rule.edges : ℝ) + 1) ^ (order - 1) := by positivity
    have hinside : (rule.vertices : ℝ) ^ order + (rule.edges : ℝ) *
        (rule.generation n).network.expectedInternalBoundaryMoment p order ≤
        ((rule.vertices : ℝ) ^ order + (rule.edges : ℝ) * momentBound) * radius ^ (order * n) := by
      nlinarith [mul_le_mul_of_nonneg_left hupper he]
    have hscaled := mul_le_mul_of_nonneg_left hinside hc
    dsimp only [rootMomentBound]
    nlinarith
  let powerBound := 2 ^ (order + 1) * atomBound * rootMomentBound
  have hpowerPositive : 0 < powerBound := by dsimp [powerBound]; positivity
  refine ⟨2 ^ (order - 1) * (atomBound + powerBound), by positivity, ?_⟩
  intro n root size
  obtain ⟨symmetry, hs, ht⟩ := h.massAdmissible.symmetric.generation n
  have hpositive : 0 < (rule.generation n).network.reliability p := by
    rwa [rule.generation_fixed_point p hfixed n]
  have hless : (rule.generation n).network.reliability p < 1 := by
    rwa [rule.generation_fixed_point p hfixed n]
  have hchild (child : LiveState) (target : ℕ) :
      (rule.generation n).network.conditionalInternalMassProbability p (child == .connected)
        true (child == .both) target ≤ atomBound / radius ^ n := by
    apply (le_div_iff₀ (pow_pos hradius0 n)).mpr
    simpa only [mul_comm] using hatom n child target
  obtain ⟨first, second, hdistinct, hfirst, hsecond⟩ :=
    h.internal_vertex_two_incident_edges root.val root.property.1 root.property.2
  have hrootAtom := rule.network.coarseRootMassObservable_atom_bound (rule.generation n).network
    symmetry hs ht p hp.le hp'.le hpositive hless (atomBound / radius ^ n) hchild root.val first hfirst size
  have hrootPower := rule.network.coarseRootMassObservable_point_power_bound (rule.generation n).network
    symmetry hs ht p hp.le hp'.le hpositive hless (atomBound / radius ^ n) (by positivity)
    hchild root.val first second hdistinct.symm hfirst hsecond order size
  have htotal := hrootPower.trans (mul_le_mul_of_nonneg_left (hrootMoment n root)
    (show 0 ≤ 2 ^ (order + 1) * (atomBound / radius ^ n) by positivity))
  have hnormalized : radius ^ n * rule.network.coarseRootMassObservable (rule.generation n).network p root.val
      (fun mass => if mass = size then 1 else 0) * ((size : ℝ) / radius ^ n) ^ order ≤ powerBound := by
    calc
      _ = (radius ^ n / (radius ^ n) ^ order) *
          ((size : ℝ) ^ order * rule.network.coarseRootMassObservable (rule.generation n).network p root.val
            (fun mass => if mass = size then 1 else 0)) := by rw [div_pow]; ring
      _ ≤ (radius ^ n / (radius ^ n) ^ order) *
          (2 ^ (order + 1) * (atomBound / radius ^ n) *
            (rootMomentBound * radius ^ (order * n))) := mul_le_mul_of_nonneg_left htotal (by positivity)
      _ = powerBound := by
        dsimp only [powerBound]
        rw [Nat.mul_comm order n, pow_mul]
        field_simp [hradius0.ne']
  apply polynomial_point_tail_of_two_bounds (radius ^ n) size
    (rule.network.coarseRootMassObservable (rule.generation n).network p root.val
      (fun mass => if mass = size then 1 else 0)) atomBound powerBound (pow_pos hradius0 n)
    (Nat.cast_nonneg _) _ order _ hnormalized
  · unfold coarseRootMassObservable
    apply Finset.sum_nonneg
    intro configuration _
    apply mul_nonneg (bernoulliWeight_nonneg hp.le hp'.le _)
    dsimp only
    split_ifs <;> norm_num
  · have hnorm := (le_div_iff₀ (pow_pos hradius0 n)).mp hrootAtom
    simpa only [mul_comm] using hnorm

/-- The actual finite birth count has arbitrary integer-order spatial point bounds. -/
theorem Classical.birth_mass_polynomial_point_tail {rule : Rule} (h : rule.Classical)
    (p : ℝ) (hp : 0 < p) (hp' : p < 1) (hfixed : rule.network.reliability p = p)
    (order : ℕ) (horder : 1 ≤ order) :
    ∃ bound : ℝ, 0 < bound ∧ ∀ (n size : ℕ),
      rule.network.expectedBirthClusterCount (rule.generation n).network p size ≤
      bound / ((spectralRadius ℂ ((rule.network.massMatrix p).map Complex.ofReal)).toReal) ^ n /
        (1 + (size : ℝ) / ((spectralRadius ℂ ((rule.network.massMatrix p).map Complex.ofReal)).toReal) ^ n) ^ order := by
  let radius := (spectralRadius ℂ ((rule.network.massMatrix p).map Complex.ofReal)).toReal
  have hradius : 1 < radius :=
    (rule.network.interior_fixed_point_strictly_unstable p hp hp' hfixed h.scale).trans
      (rule.interior_fixed_point_spectral_dominance p hp hp' hfixed h.massAdmissible.symmetric h.scale).2.1
  obtain ⟨bound, hbound, hpoint⟩ := h.coarse_root_polynomial_point_tail p hp hp' hfixed order horder
  refine ⟨((Fintype.card rule.network.InteriorVertex : ℝ) + 1) * bound, by positivity, ?_⟩
  intro n size
  have hnonnegative : 0 ≤ bound / radius ^ n / (1 + (size : ℝ) / radius ^ n) ^ order := by
    have : 0 < radius := zero_lt_one.trans hradius
    positivity
  calc
    _ ≤ ∑ root : rule.network.InteriorVertex,
        rule.network.coarseRootMassObservable (rule.generation n).network p root.val
          (fun mass => if mass = size then 1 else 0) :=
      rule.network.expectedBirthClusterCount_le_interiorRoot_laws (rule.generation n).network hp.le hp'.le size
    _ ≤ ∑ _root : rule.network.InteriorVertex,
        bound / radius ^ n / (1 + (size : ℝ) / radius ^ n) ^ order :=
      Finset.sum_le_sum (fun root _ => hpoint n root size)
    _ = (Fintype.card rule.network.InteriorVertex : ℝ) *
        (bound / radius ^ n / (1 + (size : ℝ) / radius ^ n) ^ order) := by
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    _ ≤ ((Fintype.card rule.network.InteriorVertex : ℝ) + 1) *
        (bound / radius ^ n / (1 + (size : ℝ) / radius ^ n) ^ order) := by nlinarith
    _ = _ := by ring

end
end Universality.Rule


