import IGSIII.Mass.OrientedCounts

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

namespace Universality.FiniteNetwork

open Matrix
open scoped ENNReal

/-- The four live states. The inactive state is excluded from the offspring
matrix rather than assigned an artificial positive Perron coordinate. -/
inductive MassLiveState where
  | connected | both | sourceOnly | targetOnly
  deriving DecidableEq, Fintype, Inhabited

def MassLiveState.oriented : MassLiveState → OrientedState
  | .connected => .connected
  | .both => .both
  | .sourceOnly => .sourceOnly
  | .targetOnly => .targetOnly

def MassLiveState.erase : MassLiveState → LiveState
  | .connected => .connected
  | .both => .both
  | .sourceOnly | .targetOnly => .single

def MassLiveState.sourceSelected : MassLiveState → Bool
  | .connected | .both | .sourceOnly => true
  | .targetOnly => false

def MassLiveState.targetSelected : MassLiveState → Bool
  | .both | .targetOnly => true
  | .connected | .sourceOnly => false

theorem sum_massLiveState {α : Type*} [AddCommMonoid α] (response : MassLiveState → α) :
    ∑ state, response state = response .connected + response .both + response .sourceOnly + response .targetOnly := by
  have enumeration : (Finset.univ : Finset MassLiveState) =
      {.connected, .both, .sourceOnly, .targetOnly} := by decide
  rw [enumeration]
  simp [add_assoc]

variable {vertices edges : ℕ}

/-- The genuine expected four-type child counts, sampled jointly from one
conditioned rule configuration. For C the source mask is its whole crossing
component; B and the two one-arm masks retain their stated terminals. -/
noncomputable def orientedMassMatrix (network : FiniteNetwork vertices edges) (p : ℝ) :
    Matrix MassLiveState MassLiveState ℝ :=
  fun parent child => ∑ configuration,
    network.conditionalCellWeight p (parent.erase == .connected) configuration *
      network.orientedLiveCount parent.sourceSelected parent.targetSelected configuration child.oriented

theorem orientedMassMatrix_nonnegative (network : FiniteNetwork vertices edges)
    (p : ℝ) (positive : 0 ≤ p) (below_one : p ≤ 1) :
    ∀ parent child, 0 ≤ network.orientedMassMatrix p parent child := by
  intro parent child
  apply Finset.sum_nonneg
  intro configuration _
  apply mul_nonneg (network.conditionalCellWeight_nonneg positive below_one _ _)
  unfold orientedLiveCount
  exact Finset.sum_nonneg (fun _ _ => by split_ifs <;> norm_num)

theorem orientedLiveCount_reverse (network : FiniteNetwork vertices edges)
    (configuration : Configuration edges) (child : OrientedState) :
    network.orientedLiveCount false true configuration child =
      network.reverse.orientedLiveCount true false configuration child := by
  unfold orientedLiveCount orientedChildState selectedActive
  simp only [Bool.false_and, Bool.true_and, Bool.false_or, Bool.or_false]
  rfl

/-- Erasing orientations intertwines the actual four-type offspring matrix
with II's three-type matrix. Terminal symmetry is used only for the target
one-arm parent row, through the proved reverse-network mass identity. -/
theorem orientedMassMatrix_erase_intertwining (network : FiniteNetwork vertices edges)
    (p : ℝ) (symmetry : network.NetworkSymmetry)
    (source_swap : symmetry.vertex network.source = network.target)
    (target_swap : symmetry.vertex network.target = network.source)
    (values : LiveState → ℝ) :
    network.orientedMassMatrix p *ᵥ (fun state => values state.erase) =
      fun state => (network.massMatrix p *ᵥ values) state.erase := by
  have weighted_response (state : LiveState) :
      (∑ configuration, network.conditionalCellWeight p (state == .connected) configuration *
        (network.orientedLiveCount true (state == .both) configuration .connected * values .connected +
          network.orientedLiveCount true (state == .both) configuration .both * values .both +
          (network.orientedLiveCount true (state == .both) configuration .sourceOnly +
            network.orientedLiveCount true (state == .both) configuration .targetOnly) * values .single)) =
      (network.massMatrix p *ᵥ values) state := by
    simp_rw [← network.liveResponse_oriented_split]
    exact ((network.massMatrix_mulVec_response p values state).trans
      (network.conditionalResponse_eq_weighted p state values)).symm
  have reverse_weighted_response :
      (∑ configuration, network.conditionalCellWeight p false configuration *
        (network.orientedLiveCount false true configuration .connected * values .connected +
          network.orientedLiveCount false true configuration .both * values .both +
          (network.orientedLiveCount false true configuration .sourceOnly +
            network.orientedLiveCount false true configuration .targetOnly) * values .single)) =
      (network.massMatrix p *ᵥ values) .single := by
    have reverse_weight (configuration : Configuration edges) :
        network.reverse.conditionalCellWeight p false configuration =
          network.conditionalCellWeight p false configuration := by
      simp only [conditionalCellWeight, crosses_reverse, reliability_reverse]
    simp_rw [network.orientedLiveCount_reverse]
    simp_rw [← reverse_weight]
    change (∑ configuration, network.reverse.conditionalCellWeight p false configuration *
        (network.reverse.orientedLiveCount true false configuration .connected * values .connected +
          network.reverse.orientedLiveCount true false configuration .both * values .both +
          (network.reverse.orientedLiveCount true false configuration .sourceOnly +
            network.reverse.orientedLiveCount true false configuration .targetOnly) * values .single)) = _
    have reverse_split (configuration : Configuration edges) :=
      network.reverse.liveResponse_oriented_split .single configuration values
    simp only [show (LiveState.single == LiveState.both) = false from rfl] at reverse_split
    simp_rw [← reverse_split]
    have response_mean := network.reverse.conditionalResponse_eq_weighted p .single values
    simp only [show (LiveState.single == LiveState.connected) = false from rfl] at response_mean
    rw [← response_mean, ← network.reverse.massMatrix_mulVec_response,
      symmetry.massMatrix_reverse source_swap target_swap]
  have row_sum (parent : MassLiveState) :
      (network.orientedMassMatrix p *ᵥ (fun state => values state.erase)) parent =
        ∑ configuration, network.conditionalCellWeight p (parent.erase == .connected) configuration *
          (network.orientedLiveCount parent.sourceSelected parent.targetSelected configuration .connected * values .connected +
            network.orientedLiveCount parent.sourceSelected parent.targetSelected configuration .both * values .both +
            (network.orientedLiveCount parent.sourceSelected parent.targetSelected configuration .sourceOnly +
              network.orientedLiveCount parent.sourceSelected parent.targetSelected configuration .targetOnly) * values .single) := by
    simp only [Matrix.mulVec, dotProduct, sum_massLiveState, orientedMassMatrix,
      MassLiveState.oriented, MassLiveState.erase, Finset.sum_mul, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro configuration _
    ring
  ext parent
  rw [row_sum]
  cases parent with
  | connected => simpa [MassLiveState.sourceSelected, MassLiveState.targetSelected,
      MassLiveState.erase, show (LiveState.connected == LiveState.both) = false from rfl] using weighted_response .connected
  | both => simpa [MassLiveState.sourceSelected, MassLiveState.targetSelected,
      MassLiveState.erase] using weighted_response .both
  | sourceOnly => simpa [MassLiveState.sourceSelected, MassLiveState.targetSelected,
      MassLiveState.erase, show (LiveState.single == LiveState.both) = false from rfl] using weighted_response .single
  | targetOnly => simpa [MassLiveState.sourceSelected, MassLiveState.targetSelected,
      MassLiveState.erase, show (LiveState.single == LiveState.connected) = false from rfl] using reverse_weighted_response

end Universality.FiniteNetwork

namespace Universality.Rule

open FiniteNetwork Matrix MeasureTheory
open scoped ENNReal

/-- The actual four-live-state offspring matrix has the same genuine complex
spectral radius as II's three-state matrix. Its positive right eigenvector
assigns the same weight to both oriented one-arm types. -/
theorem Classical.four_type_mass_spectralRadius {rule : Rule} (classicalRule : rule.Classical)
    (p : ℝ) (positive : 0 < p) (below_one : p < 1)
    (fixed_point : rule.network.reliability p = p) :
    spectralRadius ℂ ((rule.network.orientedMassMatrix p).map Complex.ofReal) =
      spectralRadius ℂ ((rule.network.massMatrix p).map Complex.ofReal) ∧
    ∃ right : MassLiveState → ℝ, (∀ state, 0 < right state) ∧
      right .sourceOnly = right .targetOnly ∧
      rule.network.orientedMassMatrix p *ᵥ right =
        (spectralRadius ℂ ((rule.network.massMatrix p).map Complex.ofReal)).toReal • right := by
  obtain ⟨right, right_positive, right_eigenvector, _⟩ :=
    classicalRule.exists_population_martingale p positive below_one fixed_point
  obtain ⟨symmetry, source_swap, target_swap⟩ := classicalRule.massAdmissible.symmetric
  have lifted_eigenvector : rule.network.orientedMassMatrix p *ᵥ (fun state => right state.erase) =
      (spectralRadius ℂ ((rule.network.massMatrix p).map Complex.ofReal)).toReal •
        (fun state => right state.erase) := by
    rw [rule.network.orientedMassMatrix_erase_intertwining p symmetry source_swap target_swap]
    ext state
    exact congrFun right_eigenvector state.erase
  have lifted_positive : ∀ state : MassLiveState, 0 < right state.erase :=
    fun state => right_positive state.erase
  constructor
  · exact (spectralRadius_eq_of_positive_eigenvector _ _ _
      (rule.network.orientedMassMatrix_nonnegative p positive.le below_one.le) lifted_positive
      ENNReal.toReal_nonneg lifted_eigenvector).trans
        (spectralRadius_eq_of_positive_eigenvector _ _ _
          (rule.network.massMatrix_nonneg positive.le below_one.le) right_positive
          ENNReal.toReal_nonneg right_eigenvector).symm
  · exact ⟨fun state => right state.erase, lifted_positive, rfl, lifted_eigenvector⟩

end Universality.Rule
