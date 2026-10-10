import IGSIII34.ResistanceLimit.FiniteEnergy

/-!
# Effective resistance for every pair of vertices of a finite network

The terminals are changed in the existing Thomson variational definition.
The resulting value is a metric on each connected component. In particular,
no triangle inequality or electrical metric is assumed as an input.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1400000

namespace IGSIII34.ResistanceLimit
noncomputable section
open Resistance Resistance.FiniteNetwork
open scoped BigOperators

variable {Vertex Edge : Type*} [Fintype Vertex] [DecidableEq Vertex]
  [Fintype Edge] [DecidableEq Edge]

def retarget (network : Resistance.FiniteNetwork Vertex Edge) (first last : Vertex) (distinct : first ≠ last) :
    Resistance.FiniteNetwork Vertex Edge where
  endpoint := network.endpoint
  source := first
  target := last
  distinct := distinct

theorem retarget_graph (network : Resistance.FiniteNetwork Vertex Edge) (first last : Vertex) (distinct : first ≠ last) :
    (retarget network first last distinct).graph = network.graph := rfl

def pairResistance (network : Resistance.FiniteNetwork Vertex Edge) (resistance : Edge → ℝ)
    (first last : Vertex) : ℝ :=
  if distinct : first ≠ last then (retarget network first last distinct).effectiveResistance resistance else 0

theorem pairResistance_self (network : Resistance.FiniteNetwork Vertex Edge) (resistance : Edge → ℝ)
    (vertex : Vertex) : pairResistance network resistance vertex vertex = 0 := by
  simp [pairResistance]

theorem pairResistance_pos (network : Resistance.FiniteNetwork Vertex Edge) (resistance : Edge → ℝ)
    (positive : ∀ edge, 0 < resistance edge) {first last : Vertex}
    (distinct : first ≠ last) (reachable : network.graph.Reachable first last) :
    0 < pairResistance network resistance first last := by
  rw [pairResistance, dif_pos distinct]
  exact (retarget network first last distinct).effectiveResistance_pos_of_connected reachable positive

theorem pairResistance_nonnegative (network : Resistance.FiniteNetwork Vertex Edge) (resistance : Edge → ℝ)
    (positive : ∀ edge, 0 < resistance edge) {first last : Vertex}
    (reachable : network.graph.Reachable first last) :
    0 ≤ pairResistance network resistance first last := by
  by_cases distinct : first ≠ last
  · exact (pairResistance_pos network resistance positive distinct reachable).le
  · simp [pairResistance, distinct]

theorem pairResistance_energy_lower_bound (network : Resistance.FiniteNetwork Vertex Edge)
    (resistance : Edge → ℝ) (positive : ∀ edge, 0 < resistance edge)
    {first last : Vertex} (distinct : first ≠ last) (reachable : network.graph.Reachable first last)
    (potential : Vertex → ℝ) :
    (potential first - potential last) ^ 2 / pairResistance network resistance first last ≤
      network.potentialEnergy resistance potential := by
  rw [pairResistance, dif_pos distinct]
  exact (retarget network first last distinct).boundaryPotential_energy_lower_bound reachable positive potential

theorem pairResistance_comm (network : Resistance.FiniteNetwork Vertex Edge) (resistance : Edge → ℝ)
    (positive : ∀ edge, 0 < resistance edge) {first last : Vertex}
    (reachable : network.graph.Reachable first last) :
    pairResistance network resistance first last = pairResistance network resistance last first := by
  by_cases distinct : first ≠ last
  · have energies : (retarget network first last distinct).boundaryPotentialEnergies resistance 0 1 =
        (retarget network last first distinct.symm).boundaryPotentialEnergies resistance 1 0 := by
      ext value
      constructor <;> rintro ⟨potential, atFirst, atLast, energy⟩
      · exact ⟨potential, atLast, atFirst, energy⟩
      · exact ⟨potential, atLast, atFirst, energy⟩
    have equality := congrArg sInf energies
    rw [(retarget network first last distinct).boundaryPotential_trace reachable positive 0 1,
      (retarget network last first distinct.symm).boundaryPotential_trace reachable.symm positive 1 0] at equality
    norm_num only [zero_sub, neg_one_sq, sub_zero, one_pow, one_div] at equality
    simpa only [pairResistance, dif_pos distinct, dif_pos distinct.symm] using inv_injective equality
  · have equal := not_ne_iff.mp distinct
    subst last
    rfl

theorem split_potentialEnergy_le (network : Resistance.FiniteNetwork Vertex Edge)
    (resistance : Edge → ℝ) (positive : ∀ edge, 0 < resistance edge)
    (potential : Vertex → ℝ) (cut : ℝ) :
    network.potentialEnergy resistance (fun vertex => min (potential vertex) cut) +
      network.potentialEnergy resistance (fun vertex => max (potential vertex - cut) 0) ≤
        network.potentialEnergy resistance potential := by
  unfold potentialEnergy
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro edge _
  rw [← add_div]
  apply div_le_div_of_nonneg_right _ (positive edge).le
  dsimp only
  by_cases firstBelow : potential (network.endpoint edge).1 ≤ cut
  · by_cases lastBelow : potential (network.endpoint edge).2 ≤ cut
    · rw [min_eq_left firstBelow, min_eq_left lastBelow,
        max_eq_right (sub_nonpos.mpr firstBelow), max_eq_right (sub_nonpos.mpr lastBelow)]
      simp
    · rw [min_eq_left firstBelow, min_eq_right (le_of_not_ge lastBelow),
        max_eq_right (sub_nonpos.mpr firstBelow), max_eq_left (sub_nonneg.mpr (le_of_not_ge lastBelow))]
      nlinarith
  · by_cases lastBelow : potential (network.endpoint edge).2 ≤ cut
    · rw [min_eq_right (le_of_not_ge firstBelow), min_eq_left lastBelow,
        max_eq_left (sub_nonneg.mpr (le_of_not_ge firstBelow)), max_eq_right (sub_nonpos.mpr lastBelow)]
      nlinarith
    · rw [min_eq_right (le_of_not_ge firstBelow), min_eq_right (le_of_not_ge lastBelow),
        max_eq_left (sub_nonneg.mpr (le_of_not_ge firstBelow)),
        max_eq_left (sub_nonneg.mpr (le_of_not_ge lastBelow))]
      ring_nf
      exact le_rfl

theorem exists_pair_minimizer_in_unitInterval (network : Resistance.FiniteNetwork Vertex Edge)
    (resistance : Edge → ℝ) (positive : ∀ edge, 0 < resistance edge)
    {first last : Vertex} (distinct : first ≠ last) (reachable : network.graph.Reachable first last) :
    ∃ potential : Vertex → ℝ, potential first = 0 ∧ potential last = 1 ∧
      (∀ vertex, 0 ≤ potential vertex ∧ potential vertex ≤ 1) ∧
      network.potentialEnergy resistance potential = (pairResistance network resistance first last)⁻¹ := by
  obtain ⟨potential, atFirst, atLast, energy⟩ :=
    (retarget network first last distinct).exists_boundaryPotential_minimizer reachable positive 0 1
  change potential first = 0 at atFirst
  change potential last = 1 at atLast
  let clipped : Vertex → ℝ := fun vertex => (Set.projIcc (0 : ℝ) 1 zero_le_one (potential vertex) : ℝ)
  have clippedFirst : clipped first = 0 := by simp [clipped, atFirst, Set.projIcc]
  have clippedLast : clipped last = 1 := by simp [clipped, atLast, Set.projIcc]
  have contraction : ∀ first last : ℝ,
      |(Set.projIcc (0 : ℝ) 1 zero_le_one first : ℝ) - (Set.projIcc (0 : ℝ) 1 zero_le_one last : ℝ)| ≤
        |first - last| := by
    intro first last
    have bound := (LipschitzWith.projIcc (show (0 : ℝ) ≤ 1 from zero_le_one)).dist_le_mul first last
    simpa only [Subtype.dist_eq, Real.dist_eq, NNReal.coe_one, one_mul] using bound
  have upper : network.potentialEnergy resistance clipped ≤ network.potentialEnergy resistance potential := by
    rw [← finiteEnergy_eq_potentialEnergy, ← finiteEnergy_eq_potentialEnergy]
    exact finiteEnergy_normal_contraction _ _ (fun edge => (inv_pos.mpr (positive edge)).le) _ contraction potential
  have lower := pairResistance_energy_lower_bound network resistance positive distinct reachable clipped
  rw [clippedFirst, clippedLast] at lower
  change network.potentialEnergy resistance potential = _ at energy
  simp only [zero_sub, neg_one_sq, one_div, pairResistance, dif_pos distinct] at energy lower
  refine ⟨clipped, clippedFirst, clippedLast, fun vertex => (Set.projIcc _ _ _ _).property, ?_⟩
  rw [pairResistance, dif_pos distinct]
  linarith

end
end IGSIII34.ResistanceLimit
