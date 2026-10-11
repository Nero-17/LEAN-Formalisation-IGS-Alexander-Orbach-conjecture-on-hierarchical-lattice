import IGSIII34.ResistanceLimit.SideSourceTrace

set_option autoImplicit false
set_option maxHeartbeats 2600000
set_option backward.isDefEq.respectTransparency false
namespace IGSIII34.ResistanceLimit
noncomputable section
open Universality Universality.FiniteNetwork IGSIII34.Percolation
open scoped BigOperators

variable {outerVertices outerEdges innerVertices innerEdges : ℕ}

def cellZeroExtension (outer : Universality.FiniteNetwork outerVertices outerEdges)
    (inner : Universality.FiniteNetwork innerVertices innerEdges)
    (chosen : Fin outerEdges) (supplied : Fin innerVertices → ℝ) : outer.SubstitutionVertex inner → ℝ :=
  Sum.elim (fun _ => 0) (fun pair => if pair.1 = chosen then supplied pair.2.val else 0)

theorem cellZeroExtension_chosen
    (outer : Universality.FiniteNetwork outerVertices outerEdges)
    (inner : Universality.FiniteNetwork innerVertices innerEdges)
    (chosen : Fin outerEdges) (supplied : Fin innerVertices → ℝ)
    (atSource : supplied inner.source = 0) (atTarget : supplied inner.target = 0)
    (vertex : Fin innerVertices) :
    cellZeroExtension outer inner chosen supplied (outer.cellVertex inner chosen vertex) = supplied vertex := by
  classical
  by_cases source : vertex = inner.source
  · subst vertex
    rw [Universality.FiniteNetwork.cellVertex_source, atSource]
    rfl
  · by_cases target : vertex = inner.target
    · subst vertex
      rw [Universality.FiniteNetwork.cellVertex_target, atTarget]
      rfl
    · simp only [Universality.FiniteNetwork.cellVertex, dif_neg source, dif_neg target,
        cellZeroExtension, Sum.elim_inr, ↓reduceIte]

theorem cellZeroExtension_other
    (outer : Universality.FiniteNetwork outerVertices outerEdges)
    (inner : Universality.FiniteNetwork innerVertices innerEdges)
    (chosen other : Fin outerEdges) (different : other ≠ chosen)
    (supplied : Fin innerVertices → ℝ) (vertex : Fin innerVertices) :
    cellZeroExtension outer inner chosen supplied (outer.cellVertex inner other vertex) = 0 := by
  classical
  by_cases source : vertex = inner.source
  · subst vertex
    rw [Universality.FiniteNetwork.cellVertex_source]
    rfl
  · by_cases target : vertex = inner.target
    · subst vertex
      rw [Universality.FiniteNetwork.cellVertex_target]
      rfl
    · simp only [Universality.FiniteNetwork.cellVertex, dif_neg source, dif_neg target,
        cellZeroExtension, Sum.elim_inr, if_neg different]

/-- The actual zero extension has exactly the supplied cell energy, with
every other socket contributing zero. This is an equality, not a bound. -/
theorem cellZeroExtension_energy
    (outer : Universality.FiniteNetwork outerVertices outerEdges)
    (inner : Universality.FiniteNetwork innerVertices innerEdges)
    (configuration : Fin outerEdges → Configuration innerEdges)
    (resistance : (Σ edge : Fin outerEdges, {child : Fin innerEdges // configuration edge child = true}) → ℝ)
    (chosen : Fin outerEdges) (supplied : Fin innerVertices → ℝ)
    (atSource : supplied inner.source = 0) (atTarget : supplied inner.target = 0) :
    (substitutedNetwork outer inner configuration).potentialEnergy resistance
      (cellZeroExtension outer inner chosen supplied) =
      (network inner (configuration chosen)).potentialEnergy (fun edge => resistance ⟨chosen, edge⟩) supplied := by
  classical
  rw [substitutedNetwork_energy_sum]
  have summands : ∀ other : Fin outerEdges,
      (network inner (configuration other)).potentialEnergy (fun edge => resistance ⟨other, edge⟩)
        (fun vertex => cellZeroExtension outer inner chosen supplied (outer.cellVertex inner other vertex)) =
      if equal : other = chosen then
        (network inner (configuration chosen)).potentialEnergy (fun edge => resistance ⟨chosen, edge⟩) supplied else 0 := by
    intro other
    by_cases equal : other = chosen
    · subst other
      simp only [dif_pos rfl]
      congr 1
      funext vertex
      exact cellZeroExtension_chosen outer inner chosen supplied atSource atTarget vertex
    · simp only [dif_neg equal, cellZeroExtension_other outer inner chosen other equal]
      simp [Resistance.FiniteNetwork.potentialEnergy]
  simp only [summands]
  simp

end
end IGSIII34.ResistanceLimit
