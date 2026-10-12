import IGSIII34.Spectral.ActualWeightMassIdentityCompletion
import IGSIII.Mass.ComponentBoundaryLaw
import Mathlib.MeasureTheory.Measure.Real

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000

namespace IGSIII34.Spectral
noncomputable section
open Universality Universality.FiniteNetwork IGSIII.Chemical.Substitution IGSIII.Probability
open MeasureTheory ProbabilityTheory Filter Matrix IGSIII.Geometry
open scoped BigOperators ENNReal Topology

/-- The genuine cylinder collar: the physical descendant socket of the
sampled component touches one of its coarse planted terminals. -/
def terminalCylinderCollarCompletion (rule : Rule) (fine coarseDepth collarDepth : ℕ) :
    Set (Π depth, Fin depth → (Fin rule.edges × Bool)) :=
  ⋃ word : Fin coarseDepth → (Fin rule.edges × Bool), ⋃ side : Bool,
    ⋃ suffix ∈ actualTerminalSocketSetCompletion rule fine collarDepth side,
      ⋃ sides : Fin collarDepth → Bool,
        {path | path (coarseDepth + collarDepth) = Fin.append word (fun index => (suffix index, sides index))}

theorem terminalCylinderCollar_measurable_completion
    (rule : Rule) (fine coarseDepth collarDepth : ℕ) :
    MeasurableSet (terminalCylinderCollarCompletion rule fine coarseDepth collarDepth) := by
  classical
  unfold terminalCylinderCollarCompletion
  apply MeasurableSet.iUnion
  intro word
  apply MeasurableSet.iUnion
  intro side
  apply MeasurableSet.iUnion
  intro suffix
  apply MeasurableSet.iUnion
  intro _
  apply MeasurableSet.iUnion
  intro sides
  exact measurableSet_eq_fun (measurable_pi_apply _) measurable_const

theorem terminalCylinderCollar_weight_union_bound_completion
    (rule : Rule) (fine coarseDepth collarDepth : ℕ)
    (boundary : Measure (Π depth, Fin depth → (Fin rule.edges × Bool)))
    (weight : List (Fin rule.edges × Bool) → ℝ)
    (nonnegative : ∀ address, 0 ≤ weight address)
    (atoms : ∀ depth word, boundary {path | path depth = word} = ENNReal.ofReal (weight (List.ofFn word))) :
    boundary.real (terminalCylinderCollarCompletion rule fine coarseDepth collarDepth) ≤
      ∑ word : Fin coarseDepth → (Fin rule.edges × Bool), ∑ side : Bool,
        ∑ suffix ∈ actualTerminalSocketSetCompletion rule fine collarDepth side,
          ∑ sides : Fin collarDepth → Bool,
            weight (List.ofFn word ++ List.ofFn (fun index => (suffix index, sides index))) := by
  classical
  unfold terminalCylinderCollarCompletion
  apply (measureReal_iUnion_fintype_le _).trans
  apply Finset.sum_le_sum
  intro word _
  apply (measureReal_iUnion_fintype_le _).trans
  apply Finset.sum_le_sum
  intro side _
  apply (measureReal_biUnion_finset_le _ _).trans
  apply Finset.sum_le_sum
  intro suffix _
  apply (measureReal_iUnion_fintype_le _).trans
  apply Finset.sum_le_sum
  intro sides _
  rw [Measure.real_def, atoms, ENNReal.toReal_ofReal (nonnegative _), List.ofFn_fin_append]

/-- The genuine boundary collar mass is dominated by the actual common-
innovation envelope. The only weight premise is its original vertex-ratio
definition; all continuation and socket-count conclusions are derived. -/
theorem actual_boundary_collar_mass_domination_completion
    (rule : Rule) (classicalRule : rule.Classical) (p : ℝ)
    (positive : 0 < p) (belowOne : p < 1)
    (fixedPoint : rule.network.reliability p = p)
    (continuation : ActualMassContinuationCompletion rule p positive belowOne fixedPoint)
    (weight : List (Fin rule.edges × Bool) →
      (((List (Fin rule.edges) × Bool) → Configuration rule.edges) → ℝ))
    (actualRatios : ∀ᵐ marks ∂independentInnovationLaw rule p positive belowOne fixedPoint,
      ∀ address, Tendsto (fun depth =>
        markedOrientedVertexMass rule marks depth (componentEdgeAddress address) (retainedComponentState rule marks address) /
          markedOrientedVertexMass rule marks (depth + address.length) [] .connected)
        atTop (𝓝 (weight address marks)))
    (nonnegative : ∀ᵐ marks ∂independentInnovationLaw rule p positive belowOne fixedPoint,
      ∀ address, 0 ≤ weight address marks) :
    ∀ᵐ marks ∂independentInnovationLaw rule p positive belowOne fixedPoint,
      ∀ (fine coarseDepth collarDepth : ℕ)
        (boundary : Measure (Π depth, Fin depth → (Fin rule.edges × Bool))),
      (∀ depth word, boundary {path | path depth = word} = ENNReal.ofReal (weight (List.ofFn word) marks)) →
      continuation.mass .connected marks *
        boundary.real (terminalCylinderCollarCompletion rule fine coarseDepth collarDepth) ≤
      actualTerminalCollarEnvelopeCompletion rule p positive belowOne fixedPoint
        continuation fine coarseDepth collarDepth marks /
          ((spectralRadius ℂ ((rule.network.massMatrix p).map Complex.ofReal)).toReal)^(coarseDepth + collarDepth) := by
  classical
  have radiusPositive : 0 < (spectralRadius ℂ ((rule.network.massMatrix p).map Complex.ofReal)).toReal :=
    zero_lt_one.trans ((rule.network.interior_fixed_point_strictly_unstable p positive belowOne fixedPoint classicalRule.scale).trans
      (rule.interior_fixed_point_spectral_dominance p positive belowOne fixedPoint
        classicalRule.massAdmissible.symmetric classicalRule.scale).2.1)
  have inactive : ∀ᵐ marks ∂independentInnovationLaw rule p positive belowOne fixedPoint,
      ∀ address, continuation.mass .inactive (innovationTreeShift rule address marks) = 0 := by
    apply ae_all_iff.mpr
    intro address
    exact (innovationTreeShift_preserving rule p positive belowOne fixedPoint address).quasiMeasurePreserving.ae continuation.inactive
  filter_upwards [actual_vertex_ratio_weight_mass_identity_completion rule classicalRule p positive belowOne
      fixedPoint continuation weight actualRatios, nonnegative, inactive,
      actual_grouped_component_socket_mass_bound_completion rule p positive belowOne fixedPoint continuation]
    with marks identity nonnegative inactive grouped
  intro fine coarseDepth collarDepth boundary atoms
  have groupBound (word : Fin coarseDepth → (Fin rule.edges × Bool))
      (suffix : Fin collarDepth → Fin rule.edges) :
      (∑ sides : Fin collarDepth → Bool,
        continuation.mass .connected marks *
          weight (List.ofFn word ++ List.ofFn (fun index => (suffix index, sides index))) marks) ≤
      (∑ parent : OrientedState,
        actualLiveIndicatorCompletion rule (List.ofFn word) marks * continuation.mass parent
          (innovationTreeShift rule (componentEdgeAddress (List.ofFn word) ++ List.ofFn suffix) marks)) /
        ((spectralRadius ℂ ((rule.network.massMatrix p).map Complex.ofReal)).toReal)^(coarseDepth + collarDepth) := by
    have massIdentity (sides : Fin collarDepth → Bool) := identity.2
      (List.ofFn word ++ List.ofFn (fun index => (suffix index, sides index)))
    have massSum : (∑ sides : Fin collarDepth → Bool,
        continuation.mass .connected marks *
          weight (List.ofFn word ++ List.ofFn (fun index => (suffix index, sides index))) marks) =
      (∑ sides : Fin collarDepth → Bool,
        continuation.mass
          (retainedComponentStateFrom rule marks (componentEdgeAddress (List.ofFn word))
            (retainedComponentState rule marks (List.ofFn word))
            (List.ofFn (fun index => (suffix index, sides index))))
          (innovationTreeShift rule (componentEdgeAddress (List.ofFn word) ++ List.ofFn suffix) marks)) /
        ((spectralRadius ℂ ((rule.network.massMatrix p).map Complex.ofReal)).toReal)^(coarseDepth + collarDepth) := by
      rw [Finset.sum_div]
      apply Finset.sum_congr rfl
      intro sides _
      simpa only [List.length_append, List.length_ofFn, retainedComponentState,
        retainedComponentStateFrom_append, List.nil_append, componentEdgeAddress, List.map_append,
        List.map_ofFn, Function.comp_def] using massIdentity sides
    rw [massSum]
    apply div_le_div_of_nonneg_right _ (pow_nonneg radiusPositive.le _)
    dsimp only [actualLiveIndicatorCompletion]
    split_ifs with live
    · simpa only [one_mul] using grouped collarDepth (componentEdgeAddress (List.ofFn word))
        (retainedComponentState rule marks (List.ofFn word)) suffix
    · have dead : retainedComponentState rule marks (List.ofFn word) = .inactive := not_ne_iff.mp live
      simp only [dead, retainedComponentStateFrom_inactive, inactive, zero_mul, Finset.sum_const_zero]
      exact le_rfl
  have unionBound := mul_le_mul_of_nonneg_left
    (terminalCylinderCollar_weight_union_bound_completion rule fine coarseDepth collarDepth
      boundary (fun address => weight address marks) nonnegative atoms) identity.1.le
  apply unionBound.trans
  simp_rw [Finset.mul_sum]
  unfold actualTerminalCollarEnvelopeCompletion
  simp_rw [Finset.sum_div]
  apply Finset.sum_le_sum
  intro word _
  apply Finset.sum_le_sum
  intro side _
  apply Finset.sum_le_sum
  intro suffix _
  simpa only [Finset.sum_div] using groupBound word suffix

end
end IGSIII34.Spectral
