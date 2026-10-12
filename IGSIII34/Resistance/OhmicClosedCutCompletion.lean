import IGSIII34.Resistance.IntegrationByParts

set_option autoImplicit false
set_option maxHeartbeats 1400000
namespace IGSIII34.Resistance.FiniteNetwork
noncomputable section
variable {Vertex Edge : Type*} [Fintype Vertex] [DecidableEq Vertex]
  [Fintype Edge] [DecidableEq Edge]

def setCutCompletion (subset : Set Vertex) (vertex : Vertex) : ℝ := by
  classical
  exact if vertex ∈ subset then 1 else 0

theorem ohmic_closed_cut_nonpositive_completion
    (network : FiniteNetwork Vertex Edge) (subset : Set Vertex)
    (resistance current : Edge → ℝ) (potential : Vertex → ℝ)
    (positive : ∀ edge, 0 < resistance edge)
    (ohm : ∀ edge, resistance edge * current edge =
      potential (network.endpoint edge).1 - potential (network.endpoint edge).2)
    (closed : ∀ first last, first ∈ subset → network.graph.Adj first last →
      potential last < potential first → last ∈ subset)
    (edge : Edge) :
    current edge * (setCutCompletion subset (network.endpoint edge).1 -
      setCutCompletion subset (network.endpoint edge).2) ≤ 0 := by
  classical
  by_cases firstMember : (network.endpoint edge).1 ∈ subset
  · by_cases lastMember : (network.endpoint edge).2 ∈ subset
    · simp [setCutCompletion, firstMember, lastMember]
    · have nonpositive : current edge ≤ 0 := by
        by_contra fails
        have currentPositive : 0 < current edge := lt_of_not_ge fails
        have potentialLower : potential (network.endpoint edge).2 < potential (network.endpoint edge).1 := by
          have productPositive := mul_pos (positive edge) currentPositive
          rw [ohm] at productPositive
          linarith
        have adjacent : network.graph.Adj (network.endpoint edge).1 (network.endpoint edge).2 := by
          refine ⟨?_, edge, Or.inl rfl⟩
          intro equal
          rw [equal] at potentialLower
          exact (lt_irrefl _) potentialLower
        exact lastMember (closed _ _ firstMember adjacent potentialLower)
      simpa [setCutCompletion, firstMember, lastMember] using nonpositive
  · by_cases lastMember : (network.endpoint edge).2 ∈ subset
    · have nonnegative : 0 ≤ current edge := by
        by_contra fails
        have currentNegative : current edge < 0 := lt_of_not_ge fails
        have potentialLower : potential (network.endpoint edge).1 < potential (network.endpoint edge).2 := by
          have productNegative := mul_neg_of_pos_of_neg (positive edge) currentNegative
          rw [ohm] at productNegative
          linarith
        have adjacent : network.graph.Adj (network.endpoint edge).2 (network.endpoint edge).1 := by
          refine ⟨?_, edge, Or.inr rfl⟩
          intro equal
          rw [equal] at potentialLower
          exact (lt_irrefl _) potentialLower
        exact firstMember (closed _ _ lastMember adjacent potentialLower)
      simpa [setCutCompletion, firstMember, lastMember] using neg_nonpos.mpr nonnegative
    · simp [setCutCompletion, firstMember, lastMember]

/-- Kirchhoff's law forces the terminal on the receiving side of a strict
Ohmic cut. Both reachability directions for a nonzero edge follow by taking
forward closures and complements of backward closures. -/
theorem ohmic_closed_cut_terminals_completion
    (network : FiniteNetwork Vertex Edge) (subset : Set Vertex)
    (resistance current : Edge → ℝ) (potential : Vertex → ℝ)
    (positive : ∀ edge, 0 < resistance edge)
    (unitFlow : current ∈ network.unitFlows)
    (ohm : ∀ edge, resistance edge * current edge =
      potential (network.endpoint edge).1 - potential (network.endpoint edge).2)
    (closed : ∀ first last, first ∈ subset → network.graph.Adj first last →
      potential last < potential first → last ∈ subset)
    (edge : Edge) (currentPositive : 0 < current edge)
    (firstOutside : (network.endpoint edge).1 ∉ subset)
    (lastInside : (network.endpoint edge).2 ∈ subset) :
    network.source ∉ subset ∧ network.target ∈ subset := by
  classical
  have termsNonpositive := ohmic_closed_cut_nonpositive_completion network subset resistance current potential positive ohm closed
  have edgeNegative : current edge * (setCutCompletion subset (network.endpoint edge).1 -
      setCutCompletion subset (network.endpoint edge).2) < 0 := by
    simpa [setCutCompletion, firstOutside, lastInside] using neg_neg_of_pos currentPositive
  have single := Finset.single_le_sum (f := fun index : Edge =>
    -(current index * (setCutCompletion subset (network.endpoint index).1 -
      setCutCompletion subset (network.endpoint index).2)))
    (fun index _ => neg_nonneg.mpr (termsNonpositive index)) (Finset.mem_univ edge)
  simp only [Finset.sum_neg_distrib] at single
  have totalNegative : ∑ index : Edge,
      current index * (setCutCompletion subset (network.endpoint index).1 -
        setCutCompletion subset (network.endpoint index).2) < 0 := by linarith
  rw [network.unitFlow_integrationByParts unitFlow] at totalNegative
  by_cases sourceMember : network.source ∈ subset
  · by_cases targetMember : network.target ∈ subset <;>
      norm_num [setCutCompletion, sourceMember, targetMember] at totalNegative
  · refine ⟨sourceMember, ?_⟩
    by_contra targetOutside
    norm_num [setCutCompletion, sourceMember, targetOutside] at totalNegative

end
end IGSIII34.Resistance.FiniteNetwork
