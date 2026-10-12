import IGSIII34.Spectral.ActualMassMaximaCompletion
import IGSIII34.Spectral.ActualWeightMassIdentityCompletion
import IGSIII34.Spectral.GroupedSocketMassCompletion

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2600000

namespace IGSIII34.Spectral
noncomputable section
open Universality Universality.FiniteNetwork IGSIII.Chemical.Substitution IGSIII.Geometry IGSIII.Probability
open IGSIII34.Percolation MeasureTheory Filter Matrix
open scoped BigOperators Topology

theorem actual_mass_continuation_alladdress_subexponential_completion
    (rule : Rule) (classicalRule : rule.Classical) (p : ℝ)
    (positive : 0 < p) (belowOne : p < 1) (fixedPoint : rule.network.reliability p = p)
    (continuation : ActualMassContinuationCompletion rule p positive belowOne fixedPoint) :
    ∀ᵐ marks ∂independentInnovationLaw rule p positive belowOne fixedPoint,
      ∀ slack : ℝ, 1 < slack → ∃ threshold : ℕ,
        ∀ address parent, threshold ≤ address.length →
          continuation.mass parent (innovationTreeShift rule address marks) ≤ slack^address.length := by
  obtain ⟨limit, _, _, convergence, _, _, maxima⟩ :=
    exists_actual_mass_field_subexponential classicalRule p positive belowOne fixedPoint
  filter_upwards [convergence, continuation.actualLimits, maxima] with marks limitConvergence continuationConvergence maxima
  intro slack greater
  obtain ⟨threshold, estimates⟩ := maxima slack greater
  refine ⟨threshold, ?_⟩
  intro address parent after
  have equality := tendsto_nhds_unique (continuationConvergence address parent) (limitConvergence address parent).2.1
  rw [equality]
  exact estimates address parent after

def physicalSocketCylinderCompletion (rule : Rule) (depth : ℕ) (edges : Fin depth → Fin rule.edges) :
    Set (Π depth, Fin depth → (Fin rule.edges × Bool)) :=
  ⋃ sides : Fin depth → Bool, {path | path depth = fun index => (edges index, sides index)}

theorem physical_socket_cylinder_mem_completion (rule : Rule) (depth : ℕ)
    (edges : Fin depth → Fin rule.edges) (path : Π depth, Fin depth → (Fin rule.edges × Bool)) :
    path ∈ physicalSocketCylinderCompletion rule depth edges ↔
      ∀ index, (path depth index).1 = edges index := by
  constructor
  · rintro ⟨_, ⟨sides, rfl⟩, equality⟩
    exact fun index => congrArg Prod.fst (congrFun equality index)
  · intro coordinates
    apply Set.mem_iUnion.mpr
    refine ⟨fun index => (path depth index).2, ?_⟩
    funext index
    exact Prod.ext (coordinates index) rfl

theorem physical_socket_cylinder_measurable_completion (rule : Rule) (depth : ℕ)
    (edges : Fin depth → Fin rule.edges) :
    MeasurableSet (physicalSocketCylinderCompletion rule depth edges) := by
  apply MeasurableSet.iUnion
  intro sides
  exact measurableSet_eq_fun (measurable_pi_apply _) measurable_const

theorem physical_socket_cylinder_mass_bound_completion
    (rule : Rule) (depth : ℕ) (edges : Fin depth → Fin rule.edges)
    (boundary : Measure (Π depth, Fin depth → (Fin rule.edges × Bool)))
    (weight : List (Fin rule.edges × Bool) → ℝ)
    (nonnegative : ∀ address, 0 ≤ weight address)
    (atoms : ∀ depth word, boundary {path | path depth = word} = ENNReal.ofReal (weight (List.ofFn word))) :
    boundary.real (physicalSocketCylinderCompletion rule depth edges) ≤
      ∑ sides : Fin depth → Bool, weight (List.ofFn (fun index => (edges index, sides index))) := by
  classical
  unfold physicalSocketCylinderCompletion
  apply (measureReal_iUnion_fintype_le _).trans
  apply Finset.sum_le_sum
  intro sides _
  rw [Measure.real_def, atoms, ENNReal.toReal_ofReal (nonnegative _)]

/-- All component histories inside a single physical socket have together
the expected Perron mass exponent. The original coupled B decomposition
replaces the apparent exponentially many side choices by five mask terms. -/
theorem actual_physical_socket_mass_subexponential_completion
    (rule : Rule) (classicalRule : rule.Classical) (p : ℝ)
    (positive : 0 < p) (belowOne : p < 1) (fixedPoint : rule.network.reliability p = p)
    (continuation : ActualMassContinuationCompletion rule p positive belowOne fixedPoint)
    (weight : List (Fin rule.edges × Bool) → (((List (Fin rule.edges) × Bool) → Configuration rule.edges) → ℝ))
    (actualRatios : ∀ᵐ marks ∂independentInnovationLaw rule p positive belowOne fixedPoint,
      ∀ address, Tendsto (fun depth =>
        markedOrientedVertexMass rule marks depth (componentEdgeAddress address) (retainedComponentState rule marks address) /
          markedOrientedVertexMass rule marks (depth + address.length) [] .connected)
        atTop (𝓝 (weight address marks)))
    (nonnegative : ∀ᵐ marks ∂independentInnovationLaw rule p positive belowOne fixedPoint,
      ∀ address, 0 ≤ weight address marks) :
    ∀ᵐ marks ∂independentInnovationLaw rule p positive belowOne fixedPoint,
      ∀ slack : ℝ, 1 < slack → ∃ bound : ℝ, 0 < bound ∧ ∃ threshold : ℕ,
        ∀ depth : ℕ, threshold ≤ depth → ∀ edges : Fin depth → Fin rule.edges,
        ∀ boundary : Measure (Π depth, Fin depth → (Fin rule.edges × Bool)),
        (∀ depth word, boundary {path | path depth = word} = ENNReal.ofReal (weight (List.ofFn word) marks)) →
          boundary.real (physicalSocketCylinderCompletion rule depth edges) *
            ((spectralRadius ℂ ((rule.network.massMatrix p).map Complex.ofReal)).toReal)^depth ≤ bound * slack^depth := by
  classical
  have radiusPositive : 0 < (spectralRadius ℂ ((rule.network.massMatrix p).map Complex.ofReal)).toReal :=
    zero_lt_one.trans ((rule.network.interior_fixed_point_strictly_unstable p positive belowOne fixedPoint classicalRule.scale).trans
      (rule.interior_fixed_point_spectral_dominance p positive belowOne fixedPoint
        classicalRule.massAdmissible.symmetric classicalRule.scale).2.1)
  filter_upwards [actual_vertex_ratio_weight_mass_identity_completion rule classicalRule p positive belowOne
      fixedPoint continuation weight actualRatios, nonnegative,
    actual_grouped_component_socket_mass_bound_completion rule p positive belowOne fixedPoint continuation,
    actual_mass_continuation_alladdress_subexponential_completion rule classicalRule p positive belowOne fixedPoint continuation]
    with marks identity nonnegative grouped maxima
  intro slack greater
  obtain ⟨threshold, estimates⟩ := maxima slack greater
  refine ⟨5 / continuation.mass .connected marks, div_pos (by norm_num) identity.1, threshold, ?_⟩
  intro depth after edges boundary atoms
  have massBound := mul_le_mul_of_nonneg_left
    (physical_socket_cylinder_mass_bound_completion rule depth edges boundary (fun address => weight address marks)
      nonnegative atoms) identity.1.le
  rw [Finset.mul_sum] at massBound
  have massSum : (∑ sides : Fin depth → Bool,
      continuation.mass .connected marks * weight (List.ofFn (fun index => (edges index, sides index))) marks) =
      (∑ sides : Fin depth → Bool,
        continuation.mass (retainedComponentState rule marks (List.ofFn (fun index => (edges index, sides index))))
          (innovationTreeShift rule (List.ofFn edges) marks)) /
        ((spectralRadius ℂ ((rule.network.massMatrix p).map Complex.ofReal)).toReal)^depth := by
    rw [Finset.sum_div]
    apply Finset.sum_congr rfl
    intro sides _
    simpa only [List.length_ofFn, componentEdgeAddress, List.map_ofFn, Function.comp_def] using
      identity.2 (List.ofFn (fun index => (edges index, sides index)))
  rw [massSum] at massBound
  have groupedBound := grouped depth [] .connected edges
  simp only [List.nil_append] at groupedBound
  have bound := massBound.trans (div_le_div_of_nonneg_right groupedBound (pow_pos radiusPositive depth).le)
  have maskBound : (∑ parent : OrientedState, continuation.mass parent (innovationTreeShift rule (List.ofFn edges) marks)) ≤
      5 * slack^depth := by
    calc
      _ ≤ ∑ _parent : OrientedState, slack^depth := by
        apply Finset.sum_le_sum
        intro parent _
        simpa only [List.length_ofFn] using estimates (List.ofFn edges) parent (by simpa only [List.length_ofFn] using after)
      _ = _ := by simp; norm_num [show Fintype.card OrientedState = 5 by decide]
  have normalized := (le_div_iff₀ (pow_pos radiusPositive depth)).mp
    (bound.trans (div_le_div_of_nonneg_right maskBound (pow_pos radiusPositive depth).le))
  calc
    _ ≤ (5 * slack^depth) / continuation.mass .connected marks :=
      (le_div_iff₀ identity.1).mpr (by simpa only [mul_assoc, mul_comm, mul_left_comm] using normalized)
    _ = _ := by ring

end
end IGSIII34.Spectral
