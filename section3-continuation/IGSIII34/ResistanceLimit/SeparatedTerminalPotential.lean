import IGSIII34.ResistanceLimit.PairTriangle
import IGSIII34.ResistanceLimit.SourceEnergy

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
namespace IGSIII34.ResistanceLimit
noncomputable section
open Resistance Resistance.FiniteNetwork

variable {Vertex Edge : Type*} [Fintype Vertex] [DecidableEq Vertex]
  [Fintype Edge] [DecidableEq Edge]

def sideNetwork (network : Resistance.FiniteNetwork Vertex Edge) (sourceSide : Bool) :
    Resistance.FiniteNetwork Vertex Edge :=
  if sourceSide then network else
    { network with source := network.target, target := network.source, distinct := network.distinct.symm }

theorem sideNetwork_graph (network : Resistance.FiniteNetwork Vertex Edge) (sourceSide : Bool) :
    (sideNetwork network sourceSide).graph = network.graph := by cases sourceSide <;> rfl

theorem sideNetwork_potentialEnergy (network : Resistance.FiniteNetwork Vertex Edge) (sourceSide : Bool)
    (resistance : Edge → ℝ) (potential : Vertex → ℝ) :
    (sideNetwork network sourceSide).potentialEnergy resistance potential = network.potentialEnergy resistance potential := by
  cases sourceSide <;> rfl

theorem sourceComponentEnergy_sub_constant (network : Resistance.FiniteNetwork Vertex Edge)
    (resistance : Edge → ℝ) (potential : Vertex → ℝ) (constant : ℝ) :
    sourceComponentEnergy network resistance (fun vertex => potential vertex - constant) =
      sourceComponentEnergy network resistance potential := by
  unfold sourceComponentEnergy
  simpa only [sub_eq_add_neg] using finiteEnergy_add_constant network.endpoint _ potential (-constant)

/-- Within either terminal component of a disconnected two-terminal cell,
pair minimization may be performed with both planted terminal values zero.
This is the genuine one-port fact used for dangling cells. -/
theorem exists_pair_potential_zero_at_separated_terminals
    (network : Resistance.FiniteNetwork Vertex Edge) (resistance : Edge → ℝ)
    (positive : ∀ edge, 0 < resistance edge) (sourceSide : Bool)
    (disconnected : ¬ network.graph.Reachable network.source network.target)
    {first last : Vertex} (distinct : first ≠ last)
    (firstRetained : network.graph.Reachable (sideNetwork network sourceSide).source first)
    (lastRetained : network.graph.Reachable (sideNetwork network sourceSide).source last) :
    ∃ potential : Vertex → ℝ, potential network.source = 0 ∧ potential network.target = 0 ∧
      (potential first - potential last) ^ 2 = 1 ∧
      network.potentialEnergy resistance potential ≤ (pairResistance network resistance first last)⁻¹ := by
  have reachable := firstRetained.symm.trans lastRetained
  obtain ⟨potential, atFirst, atLast, _, minimal⟩ := exists_pair_minimizer_in_unitInterval
    network resistance positive distinct reachable
  have sideDisconnected : ¬ (sideNetwork network sourceSide).graph.Reachable
      (sideNetwork network sourceSide).source (sideNetwork network sourceSide).target := by
    cases sourceSide
    · exact fun reachable => disconnected reachable.symm
    · exact disconnected
  have firstRetained' : (sideNetwork network sourceSide).graph.Reachable
      (sideNetwork network sourceSide).source first := by rwa [sideNetwork_graph]
  have lastRetained' : (sideNetwork network sourceSide).graph.Reachable
      (sideNetwork network sourceSide).source last := by rwa [sideNetwork_graph]
  let projected := sourceProjection (sideNetwork network sourceSide)
    (fun vertex => potential vertex - potential (sideNetwork network sourceSide).source)
  have atSideSource : projected (sideNetwork network sourceSide).source = 0 := by
    simp only [projected, sourceProjection, if_pos (SimpleGraph.Reachable.refl _), sub_self]
  have atSideTarget : projected (sideNetwork network sourceSide).target = 0 := by
    simp only [projected, sourceProjection, if_neg sideDisconnected]
  refine ⟨projected, ?_, ?_, ?_, ?_⟩
  · cases sourceSide
    · exact atSideTarget
    · exact atSideSource
  · cases sourceSide
    · exact atSideSource
    · exact atSideTarget
  · simp only [projected, sourceProjection, if_pos firstRetained', if_pos lastRetained', atFirst, atLast]
    ring
  · rw [← sideNetwork_potentialEnergy network sourceSide resistance projected,
      ← sourceComponentEnergy_eq_projectedEnergy, sourceComponentEnergy_sub_constant]
    exact (sourceComponentEnergy_le_potentialEnergy (sideNetwork network sourceSide) resistance positive potential).trans
      ((sideNetwork_potentialEnergy network sourceSide resistance potential).trans minimal).le

end
end IGSIII34.ResistanceLimit
