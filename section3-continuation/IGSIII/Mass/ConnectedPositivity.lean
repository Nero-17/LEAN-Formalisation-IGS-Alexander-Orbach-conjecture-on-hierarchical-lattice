import IGSIII.Mass.ZeroAtom
import IGSIII.Mass.ConnectedChildren
import IGSIII.Mass.ScalarSmoothing

set_option autoImplicit false

namespace Universality.FiniteNetwork

open MeasureTheory
open scoped ENNReal BigOperators

/-- The actual conditional crossing mixture has zero atom at most the square
of its connected zero atom. Non-crossing configurations have weight zero. -/
theorem connected_mass_zero_le_square {vertices edges : ℕ} (network : FiniteNetwork vertices edges)
    (law : LiveState → Measure ℝ) [∀ state, IsProbabilityMeasure (law state)]
    (nonnegative : ∀ state, ∀ᵐ value ∂law state, 0 ≤ value)
    (p radius : ℝ) (positive : 0 < p) (below_one : p < 1)
    (fixed_point : network.reliability p = p) (radius_ne_zero : radius ≠ 0)
    (scale : 1 < network.fullGraph.dist network.source network.target)
    (smoothing : law .connected = finiteMixtureLaw (network.conditionalCellWeight p true)
      (network.offspringMassLaw law radius .connected)) :
    law .connected {0} ≤ (law .connected {0}) ^ 2 := by
  classical
  conv_lhs => rw [smoothing]
  simp only [finiteMixtureLaw, Measure.coe_finsetSum, Finset.sum_apply,
    Measure.smul_apply, smul_eq_mul]
  calc
    _ ≤ ∑ coarse, ENNReal.ofReal (network.conditionalCellWeight p true coarse) * (law .connected {0}) ^ 2 := by
      apply Finset.sum_le_sum
      intro coarse _
      by_cases crossing : network.crosses coarse = true
      · obtain ⟨first, second, distinct, first_connected, second_connected⟩ :=
          network.crossing_has_two_connected_children scale coarse crossing
        exact mul_le_mul_right (network.offspringMassLaw_zero_le_square law nonnegative radius radius_ne_zero
          .connected coarse first second distinct first_connected second_connected) _
      · simp [conditionalCellWeight, crossing]
    _ = (∑ coarse, ENNReal.ofReal (network.conditionalCellWeight p true coarse)) * (law .connected {0}) ^ 2 :=
      (Finset.sum_mul _ _ _).symm
    _ = _ := by
      rw [← ENNReal.ofReal_sum_of_nonneg (fun coarse _ =>
        network.conditionalCellWeight_nonneg positive.le below_one.le true coarse),
        network.sum_conditionalCellWeight p (by rwa [fixed_point]) (by rwa [fixed_point]) true,
        ENNReal.ofReal_one, one_mul]

/-- A nonnegative probability-law solution of the actual connected mixture
with positive connected mean is strictly positive almost surely. -/
theorem connected_smoothing_positive {vertices edges : ℕ} (network : FiniteNetwork vertices edges)
    (law : LiveState → Measure ℝ) [∀ state, IsProbabilityMeasure (law state)]
    (nonnegative : ∀ state, ∀ᵐ value ∂law state, 0 ≤ value)
    (p radius : ℝ) (positive : 0 < p) (below_one : p < 1)
    (fixed_point : network.reliability p = p) (radius_ne_zero : radius ≠ 0)
    (scale : 1 < network.fullGraph.dist network.source network.target)
    (positive_mean : 0 < ∫ value, value ∂law .connected)
    (smoothing : law .connected = finiteMixtureLaw (network.conditionalCellWeight p true)
      (network.offspringMassLaw law radius .connected)) :
    ∀ᵐ value ∂law .connected, 0 < value := by
  apply IGSIII.Mass.ae_positive_of_connected_child_bound (probability := law .connected)
    (fun value : ℝ => value) measurable_id (nonnegative .connected) positive_mean 2 (by norm_num)
  have atom_bound := network.connected_mass_zero_le_square law nonnegative p radius positive below_one
    fixed_point radius_ne_zero scale smoothing
  have real_bound := ENNReal.toReal_mono (by finiteness) atom_bound
  simpa [Measure.real] using real_bound

end Universality.FiniteNetwork

namespace Universality.Rule

open FiniteNetwork Matrix MeasureTheory Filter
open scoped ENNReal Topology

/-- Strict connected-limit positivity for a same-limit family of the actual
graph process. The independent-child smoothing law is derived from the
finite graph recursion by the existing Fourier-uniqueness theorem. -/
theorem Classical.internal_connected_mass_positive {rule : Rule} (classicalRule : rule.Classical)
    (p : ℝ) (positive : 0 < p) (below_one : p < 1)
    (fixed_point : rule.network.reliability p = p)
    (limit : LiveState → (Π n, rule.ConfigurationHistory n) → ℝ)
    (square_integrable : ∀ state, MemLp (limit state) 2
      (ConfigurationHistory.infiniteLaw rule p positive below_one fixed_point (state == .connected)))
    (nonnegative : ∀ state, ∀ᵐ path ∂ConfigurationHistory.infiniteLaw rule p positive below_one fixed_point
      (state == .connected), 0 ≤ limit state path)
    (positive_mean : 0 < ∫ path, limit .connected path
      ∂ConfigurationHistory.infiniteLaw rule p positive below_one fixed_point true)
    (characteristic_limit : ∀ state bound, TendstoUniformlyOn
      (fun n t => (rule.generation n).network.conditionalVertexCharacteristic p state
        (t / ((spectralRadius ℂ ((rule.network.massMatrix p).map Complex.ofReal)).toReal) ^ n))
      (charFun ((ConfigurationHistory.infiniteLaw rule p positive below_one fixed_point
        (state == .connected)).map (limit state))) atTop {t : ℝ | |t| ≤ bound}) :
    ∀ᵐ path ∂ConfigurationHistory.infiniteLaw rule p positive below_one fixed_point true,
      0 < limit .connected path := by
  let law (state : LiveState) :=
    (ConfigurationHistory.infiniteLaw rule p positive below_one fixed_point (state == .connected)).map (limit state)
  letI (state : LiveState) := Measure.isProbabilityMeasure_map (square_integrable state).aestronglyMeasurable.aemeasurable
  have law_nonnegative (state : LiveState) : ∀ᵐ value ∂law state, 0 ≤ value :=
    (ae_map_iff (square_integrable state).aestronglyMeasurable.aemeasurable measurableSet_Ici).mpr (nonnegative state)
  have law_mean : 0 < ∫ value, value ∂law .connected := by
    rw [show law .connected =
      (ConfigurationHistory.infiniteLaw rule p positive below_one fixed_point true).map (limit .connected) from rfl]
    have limit_measurable : AEMeasurable (limit .connected)
        (ConfigurationHistory.infiniteLaw rule p positive below_one fixed_point true) := by
      simpa using (square_integrable .connected).aestronglyMeasurable.aemeasurable
    rw [integral_map limit_measurable
      (f := fun value : ℝ => value) (by fun_prop)]
    exact positive_mean
  have radius_positive : 0 < (spectralRadius ℂ ((rule.network.massMatrix p).map Complex.ofReal)).toReal :=
    zero_lt_one.trans ((rule.network.interior_fixed_point_strictly_unstable p positive below_one fixed_point
      classicalRule.scale).trans (rule.interior_fixed_point_spectral_dominance p positive below_one fixed_point
      classicalRule.massAdmissible.symmetric classicalRule.scale).2.1)
  have positivity := rule.network.connected_smoothing_positive law law_nonnegative p _ positive below_one
    fixed_point radius_positive.ne' classicalRule.scale law_mean
    (classicalRule.mass_limit_distribution_smoothing p positive below_one fixed_point limit square_integrable
      characteristic_limit .connected)
  exact (ae_map_iff (square_integrable .connected).aestronglyMeasurable.aemeasurable measurableSet_Ioi).mp positivity

end Universality.Rule
