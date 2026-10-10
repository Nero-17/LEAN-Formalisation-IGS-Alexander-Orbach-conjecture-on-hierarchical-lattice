import IGSIII.Mass.OrientedMatrix

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

namespace Universality.FiniteNetwork

open Matrix

variable {vertices edges : ℕ}

/-- The two one-arm parent rows agree after erasing the child orientation.
These are identities of the actual conditioned offspring matrix. -/
theorem oriented_one_arm_rows (network : FiniteNetwork vertices edges) (p : ℝ)
    (symmetry : network.NetworkSymmetry)
    (source_swap : symmetry.vertex network.source = network.target)
    (target_swap : symmetry.vertex network.target = network.source) :
    (∀ parent : MassLiveState, parent = .sourceOnly ∨ parent = .targetOnly →
      network.orientedMassMatrix p parent .connected = network.massMatrix p .single .connected) ∧
    network.orientedMassMatrix p .sourceOnly .both = network.orientedMassMatrix p .targetOnly .both ∧
    network.orientedMassMatrix p .sourceOnly .sourceOnly + network.orientedMassMatrix p .sourceOnly .targetOnly =
      network.orientedMassMatrix p .targetOnly .sourceOnly + network.orientedMassMatrix p .targetOnly .targetOnly := by
  have columns (state : LiveState) := network.orientedMassMatrix_erase_intertwining p symmetry
    source_swap target_swap (fun child => if child = state then 1 else 0)
  have source_columns (state : LiveState) := congrFun (columns state) .sourceOnly
  have target_columns (state : LiveState) := congrFun (columns state) .targetOnly
  simp only [Matrix.mulVec, dotProduct, sum_massLiveState, sum_liveState,
    MassLiveState.erase, mul_ite, mul_one, mul_zero] at source_columns target_columns
  constructor
  · intro parent kind
    rcases kind with rfl | rfl
    · simpa using source_columns .connected
    · simpa using target_columns .connected
  constructor
  · have source := source_columns .both
    have target := target_columns .both
    simp at source target
    exact source.trans target.symm
  · have source := source_columns .single
    have target := target_columns .single
    simp at source target
    exact source.trans target.symm

/-- The extra orientation direction is an actual left eigenvector. The
other three directions are exactly those detected by orientation erasure. -/
theorem oriented_one_arm_difference_eigenvector (network : FiniteNetwork vertices edges) (p : ℝ)
    (symmetry : network.NetworkSymmetry)
    (source_swap : symmetry.vertex network.source = network.target)
    (target_swap : symmetry.vertex network.target = network.source) :
    (fun state : MassLiveState => if state = .sourceOnly then (1 : ℝ) else
      if state = .targetOnly then -1 else 0) ᵥ* network.orientedMassMatrix p =
    (network.orientedMassMatrix p .sourceOnly .sourceOnly -
      network.orientedMassMatrix p .targetOnly .sourceOnly) •
        (fun state : MassLiveState => if state = .sourceOnly then (1 : ℝ) else
          if state = .targetOnly then -1 else 0) := by
  obtain ⟨connected, both, single⟩ := network.oriented_one_arm_rows p symmetry source_swap target_swap
  have connected_equal := (connected .sourceOnly (Or.inl rfl)).trans
    (connected .targetOnly (Or.inr rfl)).symm
  ext child
  cases child <;>
    simp [Matrix.vecMul, dotProduct, sum_massLiveState, Pi.smul_apply, smul_eq_mul] <;>
    linarith

end Universality.FiniteNetwork

namespace Universality.Rule

open FiniteNetwork Matrix

/-- The one remaining orientation eigenvalue has strictly smaller modulus
than the mass Perron root. Positive connected offspring in both one-arm rows
give the strict contraction directly. -/
theorem Classical.oriented_mass_gap {rule : Rule} (classicalRule : rule.Classical)
    (p : ℝ) (positive : 0 < p) (below_one : p < 1)
    (fixed_point : rule.network.reliability p = p) :
    |rule.network.orientedMassMatrix p .sourceOnly .sourceOnly -
      rule.network.orientedMassMatrix p .targetOnly .sourceOnly| <
      (spectralRadius ℂ ((rule.network.massMatrix p).map Complex.ofReal)).toReal := by
  obtain ⟨right, right_positive, right_eigenvector, _⟩ :=
    classicalRule.exists_population_martingale p positive below_one fixed_point
  obtain ⟨symmetry, source_swap, target_swap⟩ := classicalRule.massAdmissible.symmetric
  have connected_column := (rule.network.massPlaneBlock_pos_of_geometry positive below_one
    (classicalRule.connected _) classicalRule.scale classicalRule.cut).2
  have row_identities := rule.network.oriented_one_arm_rows p symmetry source_swap target_swap
  have lifted_eigenvector := rule.network.orientedMassMatrix_erase_intertwining p symmetry
    source_swap target_swap right
  have nonnegative := rule.network.orientedMassMatrix_nonnegative p positive.le below_one.le
  have one_arm_sum_bound (parent : MassLiveState) (kind : parent = .sourceOnly ∨ parent = .targetOnly) :
      rule.network.orientedMassMatrix p parent .sourceOnly +
        rule.network.orientedMassMatrix p parent .targetOnly <
      (spectralRadius ℂ ((rule.network.massMatrix p).map Complex.ofReal)).toReal := by
    have equality := congrFun lifted_eigenvector parent
    rw [right_eigenvector] at equality
    have erased : parent.erase = .single := by rcases kind with rfl | rfl <;> rfl
    rw [erased] at equality
    simp only [Matrix.mulVec, dotProduct, sum_massLiveState, MassLiveState.erase,
      Pi.smul_apply, smul_eq_mul] at equality
    have connected_positive : 0 < rule.network.orientedMassMatrix p parent .connected := by
      rw [row_identities.1 parent kind]
      exact connected_column .single
    have birth_positive := mul_pos connected_positive (right_positive .connected)
    have other_nonnegative := mul_nonneg (nonnegative parent .both) (right_positive .both).le
    nlinarith [right_positive .single]
  have source_bound := one_arm_sum_bound .sourceOnly (Or.inl rfl)
  have target_bound := one_arm_sum_bound .targetOnly (Or.inr rfl)
  apply abs_lt.mpr
  constructor <;>
    linarith [nonnegative .sourceOnly .sourceOnly, nonnegative .sourceOnly .targetOnly,
      nonnegative .targetOnly .sourceOnly, nonnegative .targetOnly .targetOnly]

end Universality.Rule
