import Universality.Probability.ShiftedPowerFourier
import Universality.Probability.PositivePowerDensity
import Universality.Percolation.AllClosedBirthCharacteristic
import Universality.Percolation.InternalMassLocalLimit
import Universality.Percolation.ActualMassFullSupport
import Universality.Percolation.ClassicalClusterNumber

namespace Universality.Rule
noncomputable section
open FiniteNetwork Matrix MeasureTheory Filter
open scoped Topology ENNReal
set_option maxHeartbeats 0
set_option backward.isDefEq.respectTransparency false

/-- A genuine all-closed coarse event supplies a positive birth-size point lower bound
uniformly throughout one critical spatial scale. -/
theorem Classical.birth_mass_point_lower_from_interior_root {rule : Rule} (h : rule.Classical)
    (p : ℝ) (hp : 0 < p) (hp' : p < 1) (hfixed : rule.network.reliability p = p)
    (root : rule.network.InteriorVertex) :
    ∃ lower : ℝ, 0 < lower ∧ ∀ᶠ n : ℕ in atTop, ∀ size : ℕ,
      1 ≤ (size : ℝ) / ((spectralRadius ℂ ((rule.network.massMatrix p).map Complex.ofReal)).toReal) ^ n →
      (size : ℝ) / ((spectralRadius ℂ ((rule.network.massMatrix p).map Complex.ofReal)).toReal) ^ n ≤
        (spectralRadius ℂ ((rule.network.massMatrix p).map Complex.ofReal)).toReal →
      lower / ((spectralRadius ℂ ((rule.network.massMatrix p).map Complex.ofReal)).toReal) ^ n ≤
        rule.network.expectedBirthClusterCount (rule.generation n).network p size := by
  let radius := (spectralRadius ℂ ((rule.network.massMatrix p).map Complex.ofReal)).toReal
  have hradius : 1 < radius :=
    (rule.network.interior_fixed_point_strictly_unstable p hp hp' hfixed h.scale).trans
      (rule.interior_fixed_point_spectral_dominance p hp hp' hfixed h.massAdmissible.symmetric h.scale).2.1
  have hradius0 : 0 < radius := zero_lt_one.trans hradius
  let count := (rule.network.incidentEdges root.val).card
  have hcount : 2 ≤ count := h.internal_incidentEdges_card_ge_two root.val root.property.1 root.property.2
  obtain ⟨limit, hmem, hnonnegative, hmean, huniform, hlocal⟩ := h.internal_mass_local_limit p hp hp' hfixed
  let law := (ConfigurationHistory.infiniteLaw rule p hp hp' hfixed false).map (limit .single)
  letI : IsProbabilityMeasure law := Measure.isProbabilityMeasure_map
    (show AEMeasurable (limit .single) (ConfigurationHistory.infiniteLaw rule p hp hp' hfixed false) from
      (hmem .single).aestronglyMeasurable.aemeasurable)
  have hsupport : ∀ x : ℝ, 0 < x → x ∈ law.support :=
    h.internal_single_mass_full_support p hp hp' hfixed limit hmem hnonnegative (hmean .connected) huniform
  have hdensity := inverseCharacteristic_power_positive law (hlocal .single).1 hsupport count hcount
  obtain ⟨constant, hconstant, depth, hquadratic⟩ := h.internal_mass_fourier_polynomial_bound p hp hp' hfixed 2
  have hL1 := truncated_shifted_power_L1_convergence
    (fun n t => (rule.generation n).network.conditionalVertexCharacteristic p .single (t / radius ^ n))
    (charFun law) radius constant hradius hconstant
    (fun n => (((rule.generation n).network.continuous_conditionalVertexCharacteristic p .single).comp
      (by fun_prop)).aestronglyMeasurable)
    continuous_charFun.aestronglyMeasurable
    (fun t => (huniform .single |t|).tendsto_at (x := t) (show |t| ≤ |t| from le_rfl))
    (fun n t => (rule.generation n).network.norm_conditionalInternalCharacteristic_le_one p hp.le hp'.le
      (by rwa [rule.generation_fixed_point p hfixed n]) (by rwa [rule.generation_fixed_point p hfixed n]) _ _ _ _)
    (by
      filter_upwards [eventually_ge_atTop depth] with n hn
      exact hquadratic n hn .single) count (by omega)
  let weight (n : ℕ) (cells : Fin rule.edges → Configuration (rule.generation n).edges) : ℂ :=
    ∏ edge, ((rule.generation n).network.conditionalCellWeight p false (cells edge) : ℂ)
  let mass (n : ℕ) (cells : Fin rule.edges → Configuration (rule.generation n).edges) : ℕ :=
    (rule.network.clusterVertices (fun _ => false) root.val).card +
      ∑ edge, (rule.generation n).network.internalStateMass
        (rule.network.rootChildState root.val (fun _ => false) edge) (cells edge)
  have htruncated (n : ℕ) : truncatedLatticeCharacteristic (weight n) (mass n) (radius ^ n) =
      (Set.Ioc (-Real.pi * radius ^ n) (Real.pi * radius ^ n)).indicator
        (fun t => Complex.exp (((t / radius ^ n : ℝ) : ℂ) * Complex.I) *
          (rule.generation n).network.conditionalVertexCharacteristic p .single (t / radius ^ n) ^ count) := by
    unfold truncatedLatticeCharacteristic
    apply congrArg (Set.indicator (Set.Ioc (-Real.pi * radius ^ n) (Real.pi * radius ^ n)))
    funext t
    obtain ⟨symmetry, hs, ht⟩ := h.massAdmissible.symmetric.generation n
    simpa only [weight, mass, count, conditionalCoarseRootCharacteristic, Complex.ofReal_mul,
      Complex.ofReal_natCast, Nat.cast_add, Nat.cast_sum, Complex.ofReal_add,
      Complex.ofReal_sum] using rule.network.allClosed_coarseRoot_characteristic (rule.generation n).network
      symmetry hs ht p (by rwa [rule.generation_fixed_point p hfixed n])
      (by rwa [rule.generation_fixed_point p hfixed n]) root.val (t / radius ^ n)
  have hllt := lattice_local_limit_of_L1
    (fun n => Fin rule.edges → Configuration (rule.generation n).edges) weight mass
    (fun n => radius ^ n) (fun n => pow_pos hradius0 n)
    (fun t => charFun law t ^ count) hL1.1 (by simp_rw [htruncated]; exact hL1.2)
  have hprobabilityLLT : ∀ error > 0, ∀ᶠ n : ℕ in atTop, ∀ size : ℕ,
      ‖((radius ^ n : ℝ) : ℂ) * (rule.network.conditionalCoarseRootMassProbability (rule.generation n).network
        p root.val (fun _ => false) size : ℂ) -
        inverseCharacteristic (fun t => charFun law t ^ count) ((size : ℝ) / radius ^ n)‖ < error := by
    simpa only [weight, mass, conditionalCoarseRootMassProbability, Complex.ofReal_sum,
      Complex.ofReal_prod, Complex.ofReal_zero, Complex.ofReal_pow, apply_ite] using hllt
  obtain ⟨lower, hlower, hlowerEventually⟩ := lattice_local_limit_compact_lower
    (fun n size => rule.network.conditionalCoarseRootMassProbability (rule.generation n).network
      p root.val (fun _ => false) size) (fun n => radius ^ n) (fun n => pow_pos hradius0 n)
    (fun t => charFun law t ^ count) hdensity.1 hdensity.2 hprobabilityLLT 1 radius zero_lt_one hradius.le
  refine ⟨bernoulliWeight p (fun _ : Fin rule.edges => false) * lower,
    mul_pos (bernoulliWeight_pos hp hp' _) hlower, ?_⟩
  filter_upwards [hlowerEventually] with n hn
  intro size hfirst hsecond
  have hbirth := rule.network.expectedBirthClusterCount_ge_allClosed_root (rule.generation n).network
    hp.le hp'.le (by rwa [rule.generation_fixed_point p hfixed n])
    (by rwa [rule.generation_fixed_point p hfixed n]) root size
  rw [rule.generation_fixed_point p hfixed n] at hbirth
  calc
    _ = bernoulliWeight p (fun _ : Fin rule.edges => false) * (lower / radius ^ n) := by ring
    _ ≤ bernoulliWeight p (fun _ : Fin rule.edges => false) *
        rule.network.conditionalCoarseRootMassProbability (rule.generation n).network p root.val (fun _ => false) size :=
      mul_le_mul_of_nonneg_left (hn size hfirst hsecond) (bernoulliWeight_nonneg hp.le hp'.le _)
    _ ≤ _ := hbirth

theorem Classical.birth_mass_point_lower {rule : Rule} (h : rule.Classical)
    (p : ℝ) (hp : 0 < p) (hp' : p < 1) (hfixed : rule.network.reliability p = p) :
    ∃ lower : ℝ, 0 < lower ∧ ∀ᶠ n : ℕ in atTop, ∀ size : ℕ,
      1 ≤ (size : ℝ) / ((spectralRadius ℂ ((rule.network.massMatrix p).map Complex.ofReal)).toReal) ^ n →
      (size : ℝ) / ((spectralRadius ℂ ((rule.network.massMatrix p).map Complex.ofReal)).toReal) ^ n ≤
        (spectralRadius ℂ ((rule.network.massMatrix p).map Complex.ofReal)).toReal →
      lower / ((spectralRadius ℂ ((rule.network.massMatrix p).map Complex.ofReal)).toReal) ^ n ≤
        rule.network.expectedBirthClusterCount (rule.generation n).network p size := by
  have hnonempty : Nonempty rule.network.InteriorVertex := by
    apply Fintype.card_pos_iff.mp
    rw [rule.network.card_interior_vertices]
    have := h.vertices_gt_two
    omega
  exact h.birth_mass_point_lower_from_interior_root p hp hp' hfixed (Classical.choice hnonempty)

end
end Universality.Rule

