import IGSIII34.Diffusion.WalkEnergyIncrementCompletion20261011
import Mathlib.LinearAlgebra.FiniteDimensional.Basic

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000

namespace IGSIII34.Diffusion
noncomputable section
open Universality Universality.FiniteNetwork IGSIII.Geometry
open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators Topology NNReal

variable {Vertex Edge : Type*} [Fintype Vertex] [DecidableEq Vertex] [Fintype Edge]

def finiteWalkTransitionLinearMap (endpoint : Edge → Vertex × Vertex) :
    (Vertex → ℝ) →ₗ[ℝ] (Vertex → ℝ) where
  toFun potential first := ∑ last, transitionKernel endpoint first last * potential last
  map_add' first last := by
    funext vertex
    simp only [Pi.add_apply, mul_add, Finset.sum_add_distrib]
  map_smul' scalar potential := by
    funext vertex
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro last _
    ring

def finiteGraphResolventOperator (endpoint : Edge → Vertex × Vertex)
    (parameter acceleration : ℝ) : (Vertex → ℝ) →ₗ[ℝ] (Vertex → ℝ) :=
  parameter • LinearMap.id - acceleration • (finiteWalkTransitionLinearMap endpoint - LinearMap.id)

theorem finiteGraphResolventOperator_apply (endpoint : Edge → Vertex × Vertex)
    (positiveDegree : ∀ vertex, 0 < degree endpoint vertex)
    (parameter acceleration : ℝ) (potential : Vertex → ℝ) (vertex : Vertex) :
    finiteGraphResolventOperator endpoint parameter acceleration potential vertex =
      parameter * potential vertex - acceleration * rateOneGenerator endpoint potential vertex := by
  change parameter * potential vertex - acceleration *
    ((∑ last, transitionKernel endpoint vertex last * potential last) - potential vertex) = _
  rw [← transition_eq_kernel endpoint positiveDegree, transition_sub_identity]

theorem transition_le_at_maximum (endpoint : Edge → Vertex × Vertex)
    (positiveDegree : ∀ vertex, 0 < degree endpoint vertex)
    (potential : Vertex → ℝ) (vertex : Vertex) (maximum : ∀ last, potential last ≤ potential vertex) :
    transition endpoint potential vertex ≤ potential vertex := by
  rw [transition_eq_kernel endpoint positiveDegree]
  calc
    _ ≤ ∑ last, transitionKernel endpoint vertex last * potential vertex :=
      Finset.sum_le_sum fun last _ => mul_le_mul_of_nonneg_left
        (maximum last) (transitionKernel_nonnegative endpoint vertex last)
    _ = _ := by rw [← Finset.sum_mul, transitionKernel_sum endpoint vertex (positiveDegree vertex), one_mul]

/-- Maximum principle for the true neighbour generator at any nonnegative
acceleration. This is proved from actual stochastic row weights. -/
theorem finiteGraphResolvent_upper_bound [Nonempty Vertex]
    (endpoint : Edge → Vertex × Vertex)
    (positiveDegree : ∀ vertex, 0 < degree endpoint vertex)
    (parameter acceleration : ℝ) (parameterPositive : 0 < parameter)
    (accelerationNonnegative : 0 ≤ acceleration) (potential forcing : Vertex → ℝ)
    (equation : finiteGraphResolventOperator endpoint parameter acceleration potential = forcing)
    (bound : ℝ) (forcingBound : ∀ vertex, forcing vertex ≤ bound) :
    ∀ vertex, potential vertex ≤ bound / parameter := by
  obtain ⟨largest, _, maximum⟩ := Finset.exists_max_image Finset.univ potential Finset.univ_nonempty
  have transitionBound := transition_le_at_maximum endpoint positiveDegree potential largest
    (fun vertex => maximum vertex (Finset.mem_univ vertex))
  have generatorNonpositive : rateOneGenerator endpoint potential largest ≤ 0 := by
    dsimp only [transition] at transitionBound
    linarith
  have equationAt := congrFun equation largest
  rw [finiteGraphResolventOperator_apply endpoint positiveDegree] at equationAt
  have maximumBound : potential largest ≤ bound / parameter := by
    apply (le_div_iff₀ parameterPositive).mpr
    nlinarith [mul_nonpos_of_nonneg_of_nonpos accelerationNonnegative generatorNonpositive,
      forcingBound largest]
  exact fun vertex => (maximum vertex (Finset.mem_univ vertex)).trans maximumBound

theorem finiteGraphResolvent_absolute_bound [Nonempty Vertex]
    (endpoint : Edge → Vertex × Vertex)
    (positiveDegree : ∀ vertex, 0 < degree endpoint vertex)
    (parameter acceleration : ℝ) (parameterPositive : 0 < parameter)
    (accelerationNonnegative : 0 ≤ acceleration) (potential forcing : Vertex → ℝ)
    (equation : finiteGraphResolventOperator endpoint parameter acceleration potential = forcing)
    (bound : ℝ) (forcingBound : ∀ vertex, |forcing vertex| ≤ bound) :
    ∀ vertex, |potential vertex| ≤ bound / parameter := by
  have upper := finiteGraphResolvent_upper_bound endpoint positiveDegree parameter acceleration parameterPositive
    accelerationNonnegative potential forcing equation bound
    (fun vertex => (le_abs_self _).trans (forcingBound vertex))
  have negativeEquation : finiteGraphResolventOperator endpoint parameter acceleration (-potential) = -forcing := by
    rw [map_neg, equation]
  have lower := finiteGraphResolvent_upper_bound endpoint positiveDegree parameter acceleration parameterPositive
    accelerationNonnegative (-potential) (-forcing) negativeEquation bound
    (fun vertex => (neg_le_abs _).trans (forcingBound vertex))
  intro vertex
  exact abs_le.mpr ⟨by have := lower vertex; change -potential vertex ≤ _ at this; linarith, upper vertex⟩

theorem finiteGraphResolventOperator_injective [Nonempty Vertex]
    (endpoint : Edge → Vertex × Vertex)
    (positiveDegree : ∀ vertex, 0 < degree endpoint vertex)
    (parameter acceleration : ℝ) (parameterPositive : 0 < parameter)
    (accelerationNonnegative : 0 ≤ acceleration) :
    Function.Injective (finiteGraphResolventOperator endpoint parameter acceleration) := by
  intro first last equality
  have equation : finiteGraphResolventOperator endpoint parameter acceleration (first - last) = 0 := by
    rw [map_sub, equality, sub_self]
  have bound := finiteGraphResolvent_absolute_bound endpoint positiveDegree parameter acceleration parameterPositive
    accelerationNonnegative (first - last) 0 equation 0 (fun _ => by simp)
  funext vertex
  have zero : |first vertex - last vertex| = 0 :=
    le_antisymm (by simpa only [Pi.sub_apply, zero_div] using bound vertex) (abs_nonneg _)
  exact sub_eq_zero.mp (abs_eq_zero.mp zero)

/-- The actual finite graph resolvent is constructed by the proved finite
dimensional bijectivity of its strictly positive maximum-principle operator. -/
def finiteGraphResolvent [Nonempty Vertex]
    (endpoint : Edge → Vertex × Vertex)
    (positiveDegree : ∀ vertex, 0 < degree endpoint vertex)
    (parameter acceleration : ℝ) (parameterPositive : 0 < parameter)
    (accelerationNonnegative : 0 ≤ acceleration) (forcing : Vertex → ℝ) : Vertex → ℝ :=
  (LinearEquiv.ofBijective (finiteGraphResolventOperator endpoint parameter acceleration)
    ⟨finiteGraphResolventOperator_injective endpoint positiveDegree parameter acceleration parameterPositive
      accelerationNonnegative,
      LinearMap.injective_iff_surjective.mp (finiteGraphResolventOperator_injective endpoint positiveDegree
        parameter acceleration parameterPositive accelerationNonnegative)⟩).symm forcing

theorem finiteGraphResolvent_equation [Nonempty Vertex]
    (endpoint : Edge → Vertex × Vertex)
    (positiveDegree : ∀ vertex, 0 < degree endpoint vertex)
    (parameter acceleration : ℝ) (parameterPositive : 0 < parameter)
    (accelerationNonnegative : 0 ≤ acceleration) (forcing : Vertex → ℝ) :
    finiteGraphResolventOperator endpoint parameter acceleration
      (finiteGraphResolvent endpoint positiveDegree parameter acceleration parameterPositive accelerationNonnegative forcing) =
        forcing := by
  let equivalence := LinearEquiv.ofBijective (finiteGraphResolventOperator endpoint parameter acceleration)
    ⟨finiteGraphResolventOperator_injective endpoint positiveDegree parameter acceleration parameterPositive
      accelerationNonnegative,
      LinearMap.injective_iff_surjective.mp (finiteGraphResolventOperator_injective endpoint positiveDegree
        parameter acceleration parameterPositive accelerationNonnegative)⟩
  change equivalence (equivalence.symm forcing) = forcing
  exact equivalence.apply_symm_apply forcing

theorem finiteGraphResolvent_supremum_bound [Nonempty Vertex]
    (endpoint : Edge → Vertex × Vertex)
    (positiveDegree : ∀ vertex, 0 < degree endpoint vertex)
    (parameter acceleration : ℝ) (parameterPositive : 0 < parameter)
    (accelerationNonnegative : 0 ≤ acceleration) (forcing : Vertex → ℝ)
    (bound : ℝ) (forcingBound : ∀ vertex, |forcing vertex| ≤ bound) :
    ∀ vertex, |finiteGraphResolvent endpoint positiveDegree parameter acceleration parameterPositive
      accelerationNonnegative forcing vertex| ≤ bound / parameter :=
  finiteGraphResolvent_absolute_bound endpoint positiveDegree parameter acceleration parameterPositive
    accelerationNonnegative _ forcing (finiteGraphResolvent_equation _ _ _ _ _ _ _) bound forcingBound

theorem finiteGraphResolvent_generator_bound [Nonempty Vertex]
    (endpoint : Edge → Vertex × Vertex)
    (positiveDegree : ∀ vertex, 0 < degree endpoint vertex)
    (parameter acceleration : ℝ) (parameterPositive : 0 < parameter)
    (accelerationNonnegative : 0 ≤ acceleration) (forcing : Vertex → ℝ)
    (bound : ℝ) (forcingBound : ∀ vertex, |forcing vertex| ≤ bound) :
    ∀ vertex, |acceleration * rateOneGenerator endpoint
      (finiteGraphResolvent endpoint positiveDegree parameter acceleration parameterPositive
        accelerationNonnegative forcing) vertex| ≤ 2 * bound := by
  intro vertex
  have equation := congrFun (finiteGraphResolvent_equation endpoint positiveDegree parameter acceleration
    parameterPositive accelerationNonnegative forcing) vertex
  rw [finiteGraphResolventOperator_apply endpoint positiveDegree] at equation
  have boundPotential := finiteGraphResolvent_supremum_bound endpoint positiveDegree parameter acceleration
    parameterPositive accelerationNonnegative forcing bound forcingBound vertex
  have productBound : |parameter * finiteGraphResolvent endpoint positiveDegree parameter acceleration
      parameterPositive accelerationNonnegative forcing vertex| ≤ bound := by
    rw [abs_mul, abs_of_pos parameterPositive]
    have estimate := mul_le_mul_of_nonneg_left boundPotential parameterPositive.le
    simpa only [mul_div_cancel₀ _ parameterPositive.ne'] using estimate
  rw [show acceleration * rateOneGenerator endpoint
    (finiteGraphResolvent endpoint positiveDegree parameter acceleration parameterPositive accelerationNonnegative forcing) vertex =
    parameter * finiteGraphResolvent endpoint positiveDegree parameter acceleration parameterPositive accelerationNonnegative forcing vertex -
      forcing vertex by linarith]
  exact (abs_sub _ _).trans (by linarith [forcingBound vertex])

variable [Nonempty Vertex] [Nonempty Edge]

/-- The natural acceleration gives exactly the renormalised energy,
including every edge and its multiplicity. -/
theorem finiteGraphResolvent_energy_identity
    (endpoint : Edge → Vertex × Vertex)
    (positiveDegree : ∀ vertex, 0 < degree endpoint vertex)
    (parameter scale : ℝ) (potential forcing : Vertex → ℝ)
    (equation : finiteGraphResolventOperator endpoint parameter
      (2 * Fintype.card Edge * scale) potential = forcing) :
    parameter * (∑ vertex, degreeWeight endpoint vertex * potential vertex ^ 2) +
      scale * energy endpoint potential =
        ∑ vertex, degreeWeight endpoint vertex * forcing vertex * potential vertex := by
  rw [← exact_degree_clock endpoint positiveDegree scale potential,
    Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro vertex _
  have equationAt := congrFun equation vertex
  rw [finiteGraphResolventOperator_apply endpoint positiveDegree] at equationAt
  rw [← equationAt]
  ring

theorem finiteGraphResolvent_scaled_energy_bound
    (endpoint : Edge → Vertex × Vertex)
    (positiveDegree : ∀ vertex, 0 < degree endpoint vertex)
    (parameter scale : ℝ) (parameterPositive : 0 < parameter)
    (scaleNonnegative : 0 ≤ scale) (forcing : Vertex → ℝ)
    (bound : ℝ) (boundNonnegative : 0 ≤ bound)
    (forcingBound : ∀ vertex, |forcing vertex| ≤ bound) :
    scale * energy endpoint
      (finiteGraphResolvent endpoint positiveDegree parameter
        (2 * Fintype.card Edge * scale) parameterPositive (by positivity) forcing) ≤
      bound ^ 2 / parameter := by
  let potential := finiteGraphResolvent endpoint positiveDegree parameter
    (2 * Fintype.card Edge * scale) parameterPositive (by positivity) forcing
  have identity := finiteGraphResolvent_energy_identity endpoint positiveDegree parameter scale potential forcing
    (finiteGraphResolvent_equation endpoint positiveDegree parameter _ parameterPositive (by positivity) forcing)
  have potentialBound : ∀ vertex, |potential vertex| ≤ bound / parameter :=
    finiteGraphResolvent_supremum_bound endpoint positiveDegree parameter _ parameterPositive
      (by positivity) forcing bound forcingBound
  have pointwiseBound (vertex : Vertex) :
      forcing vertex * potential vertex ≤ bound ^ 2 / parameter := by
    calc
      _ ≤ |forcing vertex| * |potential vertex| := by rw [← abs_mul]; exact le_abs_self _
      _ ≤ bound * (bound / parameter) :=
        mul_le_mul (forcingBound vertex) (potentialBound vertex) (abs_nonneg _) boundNonnegative
      _ = _ := by ring
  have sumBound : (∑ vertex, degreeWeight endpoint vertex * forcing vertex * potential vertex) ≤
      bound ^ 2 / parameter := by
    calc
      _ ≤ ∑ vertex, degreeWeight endpoint vertex * (bound ^ 2 / parameter) :=
        Finset.sum_le_sum fun vertex _ => by
          rw [mul_assoc]
          exact mul_le_mul_of_nonneg_left (pointwiseBound vertex) (degreeWeight_nonnegative endpoint vertex)
      _ = _ := by rw [← Finset.sum_mul, degreeWeight_sum endpoint, one_mul]
  have massNonnegative : 0 ≤ ∑ vertex, degreeWeight endpoint vertex * potential vertex ^ 2 :=
    Finset.sum_nonneg fun vertex _ => mul_nonneg (degreeWeight_nonnegative endpoint vertex) (sq_nonneg _)
  have parameterMassNonnegative := mul_nonneg parameterPositive.le massNonnegative
  change scale * energy endpoint potential ≤ _
  linarith

end
end IGSIII34.Diffusion
