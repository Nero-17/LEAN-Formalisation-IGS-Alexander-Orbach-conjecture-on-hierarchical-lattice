import Mathlib.Data.Real.Basic
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Topology.Order.Compact
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity
import Mathlib.Analysis.Convex.Function

/-!
# The Thomson functional of a finite oriented network

Unit flows are defined by Kirchhoff's law at every vertex. The functional is
the infimum of their weighted quadratic energies. No resistance property is a
structure field or an axiom. This module proves monotonicity, positive
homogeneity and superadditivity directly from that definition. Identification
with the inverse Dirichlet conductance and the bound on optimal edge currents
are separate obligations.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace IGSIII34.Resistance

noncomputable section

variable {Vertex Edge : Type*} [Fintype Vertex] [DecidableEq Vertex]
  [Fintype Edge] [DecidableEq Edge]

structure FiniteNetwork (Vertex Edge : Type*) where
  endpoint : Edge → Vertex × Vertex
  source : Vertex
  target : Vertex
  distinct : source ≠ target

namespace FiniteNetwork

def divergence (network : FiniteNetwork Vertex Edge) (current : Edge → ℝ)
    (vertex : Vertex) : ℝ :=
  ∑ edge, current edge *
    ((if (network.endpoint edge).1 = vertex then 1 else 0) -
      (if (network.endpoint edge).2 = vertex then 1 else 0))

def unitFlows (network : FiniteNetwork Vertex Edge) : Set (Edge → ℝ) :=
  {current | ∀ vertex, network.divergence current vertex =
    (if vertex = network.source then 1 else 0) -
      (if vertex = network.target then 1 else 0)}

def energy (resistance current : Edge → ℝ) : ℝ :=
  ∑ edge, resistance edge * current edge ^ 2

def flowEnergies (network : FiniteNetwork Vertex Edge) (resistance : Edge → ℝ) : Set ℝ :=
  energy resistance '' network.unitFlows

def effectiveResistance (network : FiniteNetwork Vertex Edge)
    (resistance : Edge → ℝ) : ℝ := sInf (network.flowEnergies resistance)

theorem energy_nonneg {resistance : Edge → ℝ}
    (nonnegative : ∀ edge, 0 ≤ resistance edge) (current : Edge → ℝ) :
    0 ≤ energy resistance current :=
  Finset.sum_nonneg (fun edge _ => mul_nonneg (nonnegative edge) (sq_nonneg _))

theorem energy_mono {first second : Edge → ℝ}
    (comparison : ∀ edge, first edge ≤ second edge) (current : Edge → ℝ) :
    energy first current ≤ energy second current :=
  Finset.sum_le_sum (fun edge _ => mul_le_mul_of_nonneg_right (comparison edge) (sq_nonneg _))

theorem energy_add (first second current : Edge → ℝ) :
    energy (fun edge => first edge + second edge) current =
      energy first current + energy second current := by
  simp only [energy, add_mul, Finset.sum_add_distrib]

theorem energy_scale (resistance current : Edge → ℝ) (scalar : ℝ) :
    energy (fun edge => scalar * resistance edge) current = scalar * energy resistance current := by
  simp only [energy, mul_assoc, Finset.mul_sum]

theorem flowEnergies_nonempty (network : FiniteNetwork Vertex Edge)
    (feasible : network.unitFlows.Nonempty) (resistance : Edge → ℝ) :
    (network.flowEnergies resistance).Nonempty := feasible.image _

theorem flowEnergies_bddBelow (network : FiniteNetwork Vertex Edge)
    {resistance : Edge → ℝ} (nonnegative : ∀ edge, 0 ≤ resistance edge) :
    BddBelow (network.flowEnergies resistance) := by
  refine ⟨0, ?_⟩
  rintro value ⟨current, _, rfl⟩
  exact energy_nonneg nonnegative current

theorem effectiveResistance_nonneg (network : FiniteNetwork Vertex Edge)
    (feasible : network.unitFlows.Nonempty) {resistance : Edge → ℝ}
    (nonnegative : ∀ edge, 0 ≤ resistance edge) :
    0 ≤ network.effectiveResistance resistance := by
  apply le_csInf (network.flowEnergies_nonempty feasible resistance)
  rintro value ⟨current, _, rfl⟩
  exact energy_nonneg nonnegative current

theorem effectiveResistance_le_energy (network : FiniteNetwork Vertex Edge)
    {resistance current : Edge → ℝ} (nonnegative : ∀ edge, 0 ≤ resistance edge)
    (unitFlow : current ∈ network.unitFlows) :
    network.effectiveResistance resistance ≤ energy resistance current :=
  csInf_le (network.flowEnergies_bddBelow nonnegative) ⟨current, unitFlow, rfl⟩

theorem le_effectiveResistance (network : FiniteNetwork Vertex Edge)
    (feasible : network.unitFlows.Nonempty) (resistance : Edge → ℝ) (bound : ℝ)
    (lowerBound : ∀ current ∈ network.unitFlows, bound ≤ energy resistance current) :
    bound ≤ network.effectiveResistance resistance := by
  apply le_csInf (network.flowEnergies_nonempty feasible resistance)
  rintro value ⟨current, unitFlow, rfl⟩
  exact lowerBound current unitFlow

theorem effectiveResistance_mono (network : FiniteNetwork Vertex Edge)
    (feasible : network.unitFlows.Nonempty) {first second : Edge → ℝ}
    (firstNonnegative : ∀ edge, 0 ≤ first edge)
    (comparison : ∀ edge, first edge ≤ second edge) :
    network.effectiveResistance first ≤ network.effectiveResistance second := by
  apply network.le_effectiveResistance feasible second
  intro current unitFlow
  exact (network.effectiveResistance_le_energy firstNonnegative unitFlow).trans
    (energy_mono comparison current)

theorem effectiveResistance_superadditive (network : FiniteNetwork Vertex Edge)
    (feasible : network.unitFlows.Nonempty) {first second : Edge → ℝ}
    (firstNonnegative : ∀ edge, 0 ≤ first edge)
    (secondNonnegative : ∀ edge, 0 ≤ second edge) :
    network.effectiveResistance first + network.effectiveResistance second ≤
      network.effectiveResistance (fun edge => first edge + second edge) := by
  apply network.le_effectiveResistance feasible
  intro current unitFlow
  rw [energy_add]
  exact add_le_add (network.effectiveResistance_le_energy firstNonnegative unitFlow)
    (network.effectiveResistance_le_energy secondNonnegative unitFlow)

theorem effectiveResistance_scale (network : FiniteNetwork Vertex Edge)
    (feasible : network.unitFlows.Nonempty) {resistance : Edge → ℝ}
    (nonnegative : ∀ edge, 0 ≤ resistance edge) {scalar : ℝ} (scalarNonnegative : 0 ≤ scalar) :
    network.effectiveResistance (fun edge => scalar * resistance edge) =
      scalar * network.effectiveResistance resistance := by
  have infimum := isGLB_csInf (network.flowEnergies_nonempty feasible resistance)
    (network.flowEnergies_bddBelow nonnegative)
  have scaledInfimum := infimum.mul_left scalarNonnegative
  have setEquality : network.flowEnergies (fun edge => scalar * resistance edge) =
      (fun value => scalar * value) '' network.flowEnergies resistance := by
    ext value
    constructor
    · rintro ⟨current, unitFlow, rfl⟩
      exact ⟨energy resistance current, ⟨current, unitFlow, rfl⟩, (energy_scale _ _ _).symm⟩
    · rintro ⟨value, ⟨current, unitFlow, rfl⟩, rfl⟩
      exact ⟨current, unitFlow, energy_scale _ _ _⟩
  unfold effectiveResistance
  rw [setEquality]
  exact scaledInfimum.csInf_eq ((network.flowEnergies_nonempty feasible resistance).image _)

theorem effectiveResistance_weighted_superadditive (network : FiniteNetwork Vertex Edge)
    (feasible : network.unitFlows.Nonempty) {first second : Edge → ℝ}
    (firstNonnegative : ∀ edge, 0 ≤ first edge)
    (secondNonnegative : ∀ edge, 0 ≤ second edge)
    {firstScalar secondScalar : ℝ} (firstScalarNonnegative : 0 ≤ firstScalar)
    (secondScalarNonnegative : 0 ≤ secondScalar) :
    firstScalar * network.effectiveResistance first +
        secondScalar * network.effectiveResistance second ≤
      network.effectiveResistance (fun edge => firstScalar * first edge + secondScalar * second edge) := by
  rw [← network.effectiveResistance_scale feasible firstNonnegative firstScalarNonnegative,
    ← network.effectiveResistance_scale feasible secondNonnegative secondScalarNonnegative]
  exact network.effectiveResistance_superadditive feasible
    (fun edge => mul_nonneg firstScalarNonnegative (firstNonnegative edge))
    (fun edge => mul_nonneg secondScalarNonnegative (secondNonnegative edge))

theorem effectiveResistance_concaveOn (network : FiniteNetwork Vertex Edge)
    (feasible : network.unitFlows.Nonempty) :
    ConcaveOn ℝ {resistance : Edge → ℝ | ∀ edge, 0 ≤ resistance edge}
      network.effectiveResistance := by
  constructor
  · intro first firstNonnegative second secondNonnegative firstScalar secondScalar
      firstScalarNonnegative secondScalarNonnegative _ edge
    exact add_nonneg (mul_nonneg firstScalarNonnegative (firstNonnegative edge))
      (mul_nonneg secondScalarNonnegative (secondNonnegative edge))
  · intro first firstNonnegative second secondNonnegative firstScalar secondScalar
      firstScalarNonnegative secondScalarNonnegative _
    exact network.effectiveResistance_weighted_superadditive feasible firstNonnegative
      secondNonnegative firstScalarNonnegative secondScalarNonnegative

end FiniteNetwork
end
end IGSIII34.Resistance
