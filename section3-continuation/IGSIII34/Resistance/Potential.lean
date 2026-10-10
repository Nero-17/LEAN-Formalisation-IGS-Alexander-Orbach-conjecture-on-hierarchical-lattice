import IGSIII34.Resistance.Orthogonality
import Mathlib.LinearAlgebra.Dual.Lemmas

/-!
# Ohm's law obtained from Thomson minimization

The weighted minimizing current annihilates the kernel of the Kirchhoff map.
Finite linear algebra therefore expresses it as a linear combination of the
vertex divergence forms. The coefficients are a potential, not input data.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace IGSIII34.Resistance.FiniteNetwork
noncomputable section

variable {Vertex Edge : Type*} [Fintype Vertex] [DecidableEq Vertex]
  [Fintype Edge] [DecidableEq Edge]

def divergenceForm (network : FiniteNetwork Vertex Edge) (vertex : Vertex) :
    (Edge → ℝ) →ₗ[ℝ] ℝ where
  toFun := fun current => network.divergence current vertex
  map_add' := fun first second => network.divergence_add first second vertex
  map_smul' := fun scalar current => network.divergence_scale current scalar vertex

def energyDerivativeForm (resistance current : Edge → ℝ) : (Edge → ℝ) →ₗ[ℝ] ℝ where
  toFun := crossEnergy resistance current
  map_add' := by
    intro first second
    simp only [crossEnergy, mul_add, Finset.sum_add_distrib, Pi.add_apply]
  map_smul' := by
    intro scalar perturbation
    simp only [crossEnergy, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro edge _
    ring

theorem minimizing_current_has_potential (network : FiniteNetwork Vertex Edge)
    {resistance current : Edge → ℝ} (positive : ∀ edge, 0 < resistance edge)
    (unitFlow : current ∈ network.unitFlows)
    (minimal : energy resistance current = network.effectiveResistance resistance) :
    ∃ potential : Vertex → ℝ, ∀ edge,
      resistance edge * current edge =
        potential (network.endpoint edge).1 - potential (network.endpoint edge).2 := by
  have kernelInclusion : (⨅ vertex, LinearMap.ker (network.divergenceForm vertex)) ≤
      LinearMap.ker (energyDerivativeForm resistance current) := by
    intro perturbation member
    have zeroDivergence : ∀ vertex, network.divergence perturbation vertex = 0 := by
      intro vertex
      exact ((Submodule.mem_iInf _).mp member vertex)
    exact network.minimizing_current_orthogonal positive unitFlow minimal zeroDivergence
  obtain ⟨potential, representation⟩ :=
    (Submodule.mem_span_range_iff_exists_fun ℝ).mp (mem_span_of_iInf_ker_le_ker kernelInclusion)
  refine ⟨potential, ?_⟩
  intro edge
  have coefficient := LinearMap.congr_fun representation
    (fun index => if index = edge then (1 : ℝ) else 0)
  simp only [LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul] at coefficient
  change (∑ vertex, potential vertex *
      network.divergence (fun index => if index = edge then 1 else 0) vertex) =
    crossEnergy resistance current (fun index => if index = edge then 1 else 0) at coefficient
  simp_rw [network.divergence_single] at coefficient
  simpa [crossEnergy, Finset.sum_sub_distrib, mul_sub, eq_comm] using coefficient.symm

end
end IGSIII34.Resistance.FiniteNetwork
