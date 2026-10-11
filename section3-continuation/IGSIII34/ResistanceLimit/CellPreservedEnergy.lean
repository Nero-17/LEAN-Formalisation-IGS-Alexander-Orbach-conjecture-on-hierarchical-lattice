import IGSIII34.Percolation.SubstitutionTrace
import IGSIII34.ResistanceLimit.SourceEnergy

set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option backward.isDefEq.respectTransparency false
namespace IGSIII34.ResistanceLimit
noncomputable section
open Universality Universality.FiniteNetwork IGSIII34.Percolation
open Resistance Resistance.FiniteNetwork
open scoped BigOperators

variable {outerVertices outerEdges innerVertices innerEdges : ℕ}

def cellBoundaryIndicator (outer : Universality.FiniteNetwork outerVertices outerEdges)
    (chosen : Fin outerEdges) (vertex : Fin outerVertices) : ℝ :=
  if vertex = (outer.endpoint chosen).2 then 1 else 0

def cellBoundaryTestEnergy (outer : Universality.FiniteNetwork outerVertices outerEdges)
    (inner : Universality.FiniteNetwork innerVertices innerEdges)
    (configuration : Fin outerEdges → Configuration innerEdges)
    (resistance : (Σ edge : Fin outerEdges, {child : Fin innerEdges // configuration edge child = true}) → ℝ)
    (chosen : Fin outerEdges) : ℝ :=
  coarsePotentialEnergy outer inner configuration resistance (cellBoundaryIndicator outer chosen)

theorem cellTraceEnergy_nonnegative
    (inner : Universality.FiniteNetwork innerVertices innerEdges) (configuration : Configuration innerEdges)
    (resistance : {edge : Fin innerEdges // configuration edge = true} → ℝ)
    (positive : ∀ edge, 0 < resistance edge) (first last : ℝ) :
    0 ≤ cellTraceEnergy inner configuration resistance first last := by
  unfold cellTraceEnergy
  split_ifs with crossing
  · exact div_nonneg (sq_nonneg _) ((network inner configuration).effectiveResistance_pos_of_connected
      (connected_of_crosses inner configuration crossing) positive).le
  · exact le_rfl

theorem cellBoundaryTestEnergy_nonnegative
    (outer : Universality.FiniteNetwork outerVertices outerEdges)
    (inner : Universality.FiniteNetwork innerVertices innerEdges)
    (configuration : Fin outerEdges → Configuration innerEdges)
    (resistance : (Σ edge : Fin outerEdges, {child : Fin innerEdges // configuration edge child = true}) → ℝ)
    (positive : ∀ edge, 0 < resistance edge) (chosen : Fin outerEdges) :
    0 ≤ cellBoundaryTestEnergy outer inner configuration resistance chosen := by
  unfold cellBoundaryTestEnergy coarsePotentialEnergy
  exact Finset.sum_nonneg (fun edge _ => cellTraceEnergy_nonnegative inner (configuration edge)
    (fun child => resistance ⟨edge, child⟩) (fun child => positive ⟨edge, child⟩) _ _)

/-- An arbitrary potential on one actual cell extends without alteration.
All other cells are genuinely harmonically minimized, so the excess energy is
controlled by a finite coarse-boundary test energy. -/
theorem exists_cell_preserving_energy_extension
    (outer : Universality.FiniteNetwork outerVertices outerEdges)
    (inner : Universality.FiniteNetwork innerVertices innerEdges)
    (configuration : Fin outerEdges → Configuration innerEdges)
    (resistance : (Σ edge : Fin outerEdges, {child : Fin innerEdges // configuration edge child = true}) → ℝ)
    (positive : ∀ edge, 0 < resistance edge) (chosen : Fin outerEdges) (supplied : Fin innerVertices → ℝ) :
    ∃ potential : outer.SubstitutionVertex inner → ℝ,
      (∀ vertex, potential (outer.cellVertex inner chosen vertex) = supplied vertex) ∧
      (substitutedNetwork outer inner configuration).potentialEnergy resistance potential ≤
        (network inner (configuration chosen)).potentialEnergy (fun child => resistance ⟨chosen, child⟩) supplied +
        (supplied inner.source - supplied inner.target) ^ 2 *
          cellBoundaryTestEnergy outer inner configuration resistance chosen := by
  classical
  let boundary : Fin outerVertices → ℝ := fun vertex =>
    supplied inner.source + (supplied inner.target - supplied inner.source) * cellBoundaryIndicator outer chosen vertex
  have chosenSource : boundary (outer.endpoint chosen).1 = supplied inner.source := by
    simp only [boundary, cellBoundaryIndicator, if_neg (outer.loopless chosen), mul_zero, add_zero]
  have chosenTarget : boundary (outer.endpoint chosen).2 = supplied inner.target := by
    simp only [boundary, cellBoundaryIndicator, ↓reduceIte, mul_one]
    ring
  have cellMinimizer (edge : Fin outerEdges) := exists_cellTraceEnergy_minimizer inner (configuration edge)
    (fun child => resistance ⟨edge, child⟩) (fun child => positive ⟨edge, child⟩)
    (boundary (outer.endpoint edge).1) (boundary (outer.endpoint edge).2)
  let cellPotential (edge : Fin outerEdges) : Fin innerVertices → ℝ :=
    if edge = chosen then supplied else Classical.choose (cellMinimizer edge)
  have atSource (edge : Fin outerEdges) : cellPotential edge inner.source = boundary (outer.endpoint edge).1 := by
    by_cases equal : edge = chosen
    · subst edge
      simp only [cellPotential, if_pos rfl, chosenSource]
    · simp only [cellPotential, if_neg equal]
      exact (Classical.choose_spec (cellMinimizer edge)).1
  have atTarget (edge : Fin outerEdges) : cellPotential edge inner.target = boundary (outer.endpoint edge).2 := by
    by_cases equal : edge = chosen
    · subst edge
      simp only [cellPotential, if_pos rfl, chosenTarget]
    · simp only [cellPotential, if_neg equal]
      exact (Classical.choose_spec (cellMinimizer edge)).2.1
  let potential : outer.SubstitutionVertex inner → ℝ := Sum.elim boundary (fun data => cellPotential data.1 data.2.val)
  have restriction (edge : Fin outerEdges) : (fun vertex => potential (outer.cellVertex inner edge vertex)) = cellPotential edge := by
    funext vertex
    by_cases source : vertex = inner.source
    · subst vertex
      rw [Universality.FiniteNetwork.cellVertex_source]
      exact (atSource edge).symm
    · by_cases target : vertex = inner.target
      · subst vertex
        rw [Universality.FiniteNetwork.cellVertex_target]
        exact (atTarget edge).symm
      · simp only [Universality.FiniteNetwork.cellVertex, source, target, ↓reduceDIte, potential, Sum.elim_inr]
  have boundaryEnergy : coarsePotentialEnergy outer inner configuration resistance boundary =
      (supplied inner.source - supplied inner.target) ^ 2 * cellBoundaryTestEnergy outer inner configuration resistance chosen := by
    unfold cellBoundaryTestEnergy coarsePotentialEnergy
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro edge _
    unfold cellTraceEnergy
    split_ifs
    · simp only [boundary]
      ring
    · simp
  refine ⟨potential, ?_, ?_⟩
  · intro vertex
    have values := congrFun (restriction chosen) vertex
    simpa only [cellPotential, if_pos rfl] using values
  · rw [substitutedNetwork_energy_sum]
    simp only [restriction]
    calc
      _ ≤ ∑ edge, (cellTraceEnergy inner (configuration edge) (fun child => resistance ⟨edge, child⟩)
          (boundary (outer.endpoint edge).1) (boundary (outer.endpoint edge).2) +
          if edge = chosen then (network inner (configuration chosen)).potentialEnergy
            (fun child => resistance ⟨chosen, child⟩) supplied else 0) := by
        apply Finset.sum_le_sum
        intro edge _
        by_cases equal : edge = chosen
        · subst edge
          simp only [cellPotential, ↓reduceIte]
          have nonnegative := cellTraceEnergy_nonnegative inner (configuration chosen)
            (fun child => resistance ⟨chosen, child⟩) (fun child => positive ⟨chosen, child⟩)
            (boundary (outer.endpoint chosen).1) (boundary (outer.endpoint chosen).2)
          linarith
        · simp only [cellPotential, if_neg equal, add_zero]
          exact (Classical.choose_spec (cellMinimizer edge)).2.2.le
      _ = _ := by
        rw [Finset.sum_add_distrib]
        simp only [Finset.sum_ite_eq', Finset.mem_univ, if_pos]
        change coarsePotentialEnergy outer inner configuration resistance boundary + _ = _
        rw [boundaryEnergy, add_comm]

end
end IGSIII34.ResistanceLimit
