import IGSIII34.Percolation.Network
import IGSIII34.Resistance.DirichletTrace
import Universality.Graph.SubstitutionNetwork

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace IGSIII34.Percolation
noncomputable section
open Resistance
open Resistance.FiniteNetwork

variable {outerVertices outerEdges innerVertices innerEdges : ℕ}

def substitutedNetwork (outer : Universality.FiniteNetwork outerVertices outerEdges)
    (inner : Universality.FiniteNetwork innerVertices innerEdges)
    (configuration : Fin outerEdges → Universality.FiniteNetwork.Configuration innerEdges) :
    FiniteNetwork (outer.SubstitutionVertex inner)
      (Σ edge : Fin outerEdges, {child : Fin innerEdges // configuration edge child = true}) where
  endpoint edge := (outer.cellVertex inner edge.1 (inner.endpoint edge.2.val).1,
    outer.cellVertex inner edge.1 (inner.endpoint edge.2.val).2)
  source := Sum.inl outer.source
  target := Sum.inl outer.target
  distinct := fun equality => outer.terminals_distinct (Sum.inl.inj equality)

theorem substitutedNetwork_energy_sum
    (outer : Universality.FiniteNetwork outerVertices outerEdges)
    (inner : Universality.FiniteNetwork innerVertices innerEdges)
    (configuration : Fin outerEdges → Universality.FiniteNetwork.Configuration innerEdges)
    (resistance : (Σ edge : Fin outerEdges, {child : Fin innerEdges // configuration edge child = true}) → ℝ)
    (potential : outer.SubstitutionVertex inner → ℝ) :
    (substitutedNetwork outer inner configuration).potentialEnergy resistance potential =
      ∑ edge, (network inner (configuration edge)).potentialEnergy
        (fun child => resistance ⟨edge, child⟩) (fun vertex => potential (outer.cellVertex inner edge vertex)) := by
  simp only [potentialEnergy, substitutedNetwork, network, Fintype.sum_sigma]

def cellTraceEnergy
    (inner : Universality.FiniteNetwork innerVertices innerEdges)
    (configuration : Universality.FiniteNetwork.Configuration innerEdges)
    (resistance : {child : Fin innerEdges // configuration child = true} → ℝ)
    (sourceValue targetValue : ℝ) : ℝ :=
  if inner.crosses configuration then
    (sourceValue - targetValue) ^ 2 / (network inner configuration).effectiveResistance resistance else 0

theorem cellTraceEnergy_le_potentialEnergy
    (inner : Universality.FiniteNetwork innerVertices innerEdges)
    (configuration : Universality.FiniteNetwork.Configuration innerEdges)
    (resistance : {child : Fin innerEdges // configuration child = true} → ℝ)
    (positive : ∀ child, 0 < resistance child) (potential : Fin innerVertices → ℝ) :
    cellTraceEnergy inner configuration resistance (potential inner.source) (potential inner.target) ≤
      (network inner configuration).potentialEnergy resistance potential := by
  by_cases crosses : inner.crosses configuration = true
  · simpa only [cellTraceEnergy, crosses, Bool.true_eq, ↓reduceIte, network] using
      (network inner configuration).boundaryPotential_energy_lower_bound
        (connected_of_crosses inner configuration crosses) positive potential
  · simpa only [cellTraceEnergy, crosses, Bool.false_eq_true, ↓reduceIte] using
      (network inner configuration).potentialEnergy_nonnegative positive potential

theorem exists_cellTraceEnergy_minimizer
    (inner : Universality.FiniteNetwork innerVertices innerEdges)
    (configuration : Universality.FiniteNetwork.Configuration innerEdges)
    (resistance : {child : Fin innerEdges // configuration child = true} → ℝ)
    (positive : ∀ child, 0 < resistance child) (sourceValue targetValue : ℝ) :
    ∃ potential : Fin innerVertices → ℝ, potential inner.source = sourceValue ∧
      potential inner.target = targetValue ∧
      (network inner configuration).potentialEnergy resistance potential =
        cellTraceEnergy inner configuration resistance sourceValue targetValue := by
  by_cases crosses : inner.crosses configuration = true
  · simpa only [cellTraceEnergy, crosses, Bool.true_eq, ↓reduceIte, network] using
      (network inner configuration).exists_boundaryPotential_minimizer
        (connected_of_crosses inner configuration crosses) positive sourceValue targetValue
  · have disconnected : ¬ (network inner configuration).graph.Reachable
        (network inner configuration).source (network inner configuration).target := by
      change ¬ (network inner configuration).graph.Reachable inner.source inner.target
      rw [graph_eq_openGraph]
      exact fun reachable => crosses ((inner.crosses_eq_true configuration).mpr reachable)
    simpa only [cellTraceEnergy, crosses, Bool.false_eq_true, ↓reduceIte, network] using
      (network inner configuration).exists_zero_energy_boundaryPotential_of_disconnected
        disconnected resistance sourceValue targetValue

def coarsePotentialEnergy
    (outer : Universality.FiniteNetwork outerVertices outerEdges)
    (inner : Universality.FiniteNetwork innerVertices innerEdges)
    (configuration : Fin outerEdges → Universality.FiniteNetwork.Configuration innerEdges)
    (resistance : (Σ edge : Fin outerEdges, {child : Fin innerEdges // configuration edge child = true}) → ℝ)
    (potential : Fin outerVertices → ℝ) : ℝ :=
  ∑ edge, cellTraceEnergy inner (configuration edge) (fun child => resistance ⟨edge, child⟩)
    (potential (outer.endpoint edge).1) (potential (outer.endpoint edge).2)

theorem coarsePotentialEnergy_le_substituted_energy
    (outer : Universality.FiniteNetwork outerVertices outerEdges)
    (inner : Universality.FiniteNetwork innerVertices innerEdges)
    (configuration : Fin outerEdges → Universality.FiniteNetwork.Configuration innerEdges)
    (resistance : (Σ edge : Fin outerEdges, {child : Fin innerEdges // configuration edge child = true}) → ℝ)
    (positive : ∀ edge, 0 < resistance edge)
    (potential : outer.SubstitutionVertex inner → ℝ) :
    coarsePotentialEnergy outer inner configuration resistance (fun vertex => potential (Sum.inl vertex)) ≤
      (substitutedNetwork outer inner configuration).potentialEnergy resistance potential := by
  rw [substitutedNetwork_energy_sum]
  apply Finset.sum_le_sum
  intro edge _
  simpa only [Universality.FiniteNetwork.cellVertex_source, Universality.FiniteNetwork.cellVertex_target] using
    cellTraceEnergy_le_potentialEnergy inner (configuration edge) (fun child => resistance ⟨edge, child⟩)
      (fun child => positive ⟨edge, child⟩) (fun vertex => potential (outer.cellVertex inner edge vertex))

theorem exists_substituted_energy_minimizer
    (outer : Universality.FiniteNetwork outerVertices outerEdges)
    (inner : Universality.FiniteNetwork innerVertices innerEdges)
    (configuration : Fin outerEdges → Universality.FiniteNetwork.Configuration innerEdges)
    (resistance : (Σ edge : Fin outerEdges, {child : Fin innerEdges // configuration edge child = true}) → ℝ)
    (positive : ∀ edge, 0 < resistance edge) (boundary : Fin outerVertices → ℝ) :
    ∃ potential : outer.SubstitutionVertex inner → ℝ,
      (∀ vertex, potential (Sum.inl vertex) = boundary vertex) ∧
      (substitutedNetwork outer inner configuration).potentialEnergy resistance potential =
        coarsePotentialEnergy outer inner configuration resistance boundary := by
  have cellMinimizer (edge : Fin outerEdges) := exists_cellTraceEnergy_minimizer inner (configuration edge)
    (fun child => resistance ⟨edge, child⟩) (fun child => positive ⟨edge, child⟩)
    (boundary (outer.endpoint edge).1) (boundary (outer.endpoint edge).2)
  let cellPotential (edge : Fin outerEdges) := Classical.choose (cellMinimizer edge)
  have atSource (edge : Fin outerEdges) : cellPotential edge inner.source = boundary (outer.endpoint edge).1 :=
    (Classical.choose_spec (cellMinimizer edge)).1
  have atTarget (edge : Fin outerEdges) : cellPotential edge inner.target = boundary (outer.endpoint edge).2 :=
    (Classical.choose_spec (cellMinimizer edge)).2.1
  have cellEnergy (edge : Fin outerEdges) :
      (network inner (configuration edge)).potentialEnergy (fun child => resistance ⟨edge, child⟩) (cellPotential edge) =
        cellTraceEnergy inner (configuration edge) (fun child => resistance ⟨edge, child⟩)
          (boundary (outer.endpoint edge).1) (boundary (outer.endpoint edge).2) :=
    (Classical.choose_spec (cellMinimizer edge)).2.2
  let potential : outer.SubstitutionVertex inner → ℝ :=
    Sum.elim boundary (fun data => cellPotential data.1 data.2.val)
  have restriction (edge : Fin outerEdges) :
      (fun vertex => potential (outer.cellVertex inner edge vertex)) = cellPotential edge := by
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
  refine ⟨potential, (fun _ => rfl), ?_⟩
  rw [substitutedNetwork_energy_sum]
  simp only [restriction, cellEnergy, coarsePotentialEnergy]

def skeletonPotentialEnergies
    (outer : Universality.FiniteNetwork outerVertices outerEdges)
    (inner : Universality.FiniteNetwork innerVertices innerEdges)
    (configuration : Fin outerEdges → Universality.FiniteNetwork.Configuration innerEdges)
    (resistance : (Σ edge : Fin outerEdges, {child : Fin innerEdges // configuration edge child = true}) → ℝ)
    (boundary : Fin outerVertices → ℝ) : Set ℝ :=
  {value | ∃ potential : outer.SubstitutionVertex inner → ℝ,
    (∀ vertex, potential (Sum.inl vertex) = boundary vertex) ∧
    (substitutedNetwork outer inner configuration).potentialEnergy resistance potential = value}

theorem skeletonPotential_trace
    (outer : Universality.FiniteNetwork outerVertices outerEdges)
    (inner : Universality.FiniteNetwork innerVertices innerEdges)
    (configuration : Fin outerEdges → Universality.FiniteNetwork.Configuration innerEdges)
    (resistance : (Σ edge : Fin outerEdges, {child : Fin innerEdges // configuration edge child = true}) → ℝ)
    (positive : ∀ edge, 0 < resistance edge) (boundary : Fin outerVertices → ℝ) :
    sInf (skeletonPotentialEnergies outer inner configuration resistance boundary) =
      coarsePotentialEnergy outer inner configuration resistance boundary := by
  obtain ⟨potential, restriction, minimizing⟩ :=
    exists_substituted_energy_minimizer outer inner configuration resistance positive boundary
  have boundedBelow : BddBelow (skeletonPotentialEnergies outer inner configuration resistance boundary) := by
    refine ⟨0, ?_⟩
    rintro value ⟨competitor, _, rfl⟩
    exact (substitutedNetwork outer inner configuration).potentialEnergy_nonnegative positive competitor
  apply le_antisymm
  · exact csInf_le boundedBelow ⟨potential, restriction, minimizing⟩
  · apply le_csInf (show (skeletonPotentialEnergies outer inner configuration resistance boundary).Nonempty from
      ⟨_, potential, restriction, rfl⟩)
    rintro value ⟨competitor, boundaryValues, rfl⟩
    have restrictionEquality : (fun vertex => competitor (Sum.inl vertex)) = boundary := funext boundaryValues
    simpa only [restrictionEquality] using
      coarsePotentialEnergy_le_substituted_energy outer inner configuration resistance positive competitor

def coarseResistance
    (inner : Universality.FiniteNetwork innerVertices innerEdges)
    (configuration : Fin outerEdges → Universality.FiniteNetwork.Configuration innerEdges)
    (resistance : (Σ edge : Fin outerEdges, {child : Fin innerEdges // configuration edge child = true}) → ℝ) :
    {edge : Fin outerEdges // inner.coarseConfiguration configuration edge = true} → ℝ :=
  fun edge => (network inner (configuration edge.val)).effectiveResistance
    (fun child => resistance ⟨edge.val, child⟩)

theorem coarseResistance_positive
    (inner : Universality.FiniteNetwork innerVertices innerEdges)
    (configuration : Fin outerEdges → Universality.FiniteNetwork.Configuration innerEdges)
    (resistance : (Σ edge : Fin outerEdges, {child : Fin innerEdges // configuration edge child = true}) → ℝ)
    (positive : ∀ edge, 0 < resistance edge)
    (edge : {edge : Fin outerEdges // inner.coarseConfiguration configuration edge = true}) :
    0 < coarseResistance inner configuration resistance edge :=
  (network inner (configuration edge.val)).effectiveResistance_pos_of_connected
    (connected_of_crosses inner (configuration edge.val) edge.property)
    (fun child => positive ⟨edge.val, child⟩)

theorem coarsePotentialEnergy_eq_network_energy
    (outer : Universality.FiniteNetwork outerVertices outerEdges)
    (inner : Universality.FiniteNetwork innerVertices innerEdges)
    (configuration : Fin outerEdges → Universality.FiniteNetwork.Configuration innerEdges)
    (resistance : (Σ edge : Fin outerEdges, {child : Fin innerEdges // configuration edge child = true}) → ℝ)
    (potential : Fin outerVertices → ℝ) :
    coarsePotentialEnergy outer inner configuration resistance potential =
      (network outer (inner.coarseConfiguration configuration)).potentialEnergy
        (coarseResistance inner configuration resistance) potential := by
  classical
  unfold coarsePotentialEnergy cellTraceEnergy potentialEnergy coarseResistance network
  rw [← Finset.sum_filter]
  exact Finset.sum_subtype (p := fun edge => inner.coarseConfiguration configuration edge = true)
    (Finset.univ.filter fun edge => inner.crosses (configuration edge) = true)
    (fun edge => by simp [Universality.FiniteNetwork.coarseConfiguration]) _

theorem substitutedNetwork_graph_eq
    (outer : Universality.FiniteNetwork outerVertices outerEdges)
    (inner : Universality.FiniteNetwork innerVertices innerEdges)
    (configuration : Fin outerEdges → Universality.FiniteNetwork.Configuration innerEdges) :
    (substitutedNetwork outer inner configuration).graph = outer.substitutedGraph inner configuration := by
  ext first second
  constructor
  · rintro ⟨distinct, ⟨edge, child, opened⟩, orientation⟩
    rcases orientation with orientation | orientation
    · exact ⟨distinct, edge, (inner.endpoint child).1, (inner.endpoint child).2,
        ⟨inner.loopless child, child, opened, Or.inl rfl⟩,
        congrArg Prod.fst orientation, congrArg Prod.snd orientation⟩
    · exact ⟨distinct, edge, (inner.endpoint child).2, (inner.endpoint child).1,
        ⟨(inner.loopless child).symm, child, opened, Or.inr rfl⟩,
        congrArg Prod.snd orientation, congrArg Prod.fst orientation⟩
  · rintro ⟨distinct, edge, firstChild, secondChild, ⟨_, child, opened, orientation⟩, rfl, rfl⟩
    rcases orientation with orientation | orientation
    · obtain ⟨rfl, rfl⟩ := Prod.mk.inj orientation.symm
      exact ⟨distinct, ⟨edge, child, opened⟩, Or.inl rfl⟩
    · obtain ⟨rfl, rfl⟩ := Prod.mk.inj orientation.symm
      exact ⟨distinct, ⟨edge, child, opened⟩, Or.inr rfl⟩

theorem substitutedNetwork_connected
    (outer : Universality.FiniteNetwork outerVertices outerEdges)
    (inner : Universality.FiniteNetwork innerVertices innerEdges)
    (configuration : Fin outerEdges → Universality.FiniteNetwork.Configuration innerEdges)
    (crosses : outer.crosses (inner.coarseConfiguration configuration) = true) :
    (substitutedNetwork outer inner configuration).graph.Reachable
      (substitutedNetwork outer inner configuration).source
      (substitutedNetwork outer inner configuration).target := by
  change (substitutedNetwork outer inner configuration).graph.Reachable (Sum.inl outer.source) (Sum.inl outer.target)
  rw [substitutedNetwork_graph_eq]
  exact (outer.substitutedReachable_iff inner configuration outer.source outer.target).mpr
    ((outer.crosses_eq_true _).mp crosses)

theorem substitutedNetwork_conductance
    (outer : Universality.FiniteNetwork outerVertices outerEdges)
    (inner : Universality.FiniteNetwork innerVertices innerEdges)
    (configuration : Fin outerEdges → Universality.FiniteNetwork.Configuration innerEdges)
    (resistance : (Σ edge : Fin outerEdges, {child : Fin innerEdges // configuration edge child = true}) → ℝ)
    (positive : ∀ edge, 0 < resistance edge) :
    (substitutedNetwork outer inner configuration).effectiveConductance resistance =
      (network outer (inner.coarseConfiguration configuration)).effectiveConductance
        (coarseResistance inner configuration resistance) := by
  have coarsePositive := coarseResistance_positive inner configuration resistance positive
  apply le_antisymm
  · apply le_csInf ((network outer (inner.coarseConfiguration configuration)).unitPotentialEnergies_nonempty _)
    rintro value ⟨boundary, atSource, atTarget, rfl⟩
    obtain ⟨potential, restriction, minimizing⟩ :=
      exists_substituted_energy_minimizer outer inner configuration resistance positive boundary
    rw [coarsePotentialEnergy_eq_network_energy] at minimizing
    rw [← minimizing]
    exact (substitutedNetwork outer inner configuration).effectiveConductance_le_energy positive
      ((restriction outer.source).trans atSource) ((restriction outer.target).trans atTarget)
  · apply le_csInf ((substitutedNetwork outer inner configuration).unitPotentialEnergies_nonempty _)
    rintro value ⟨potential, atSource, atTarget, rfl⟩
    calc
      _ ≤ (network outer (inner.coarseConfiguration configuration)).potentialEnergy
          (coarseResistance inner configuration resistance) (fun vertex => potential (Sum.inl vertex)) :=
        (network outer (inner.coarseConfiguration configuration)).effectiveConductance_le_energy coarsePositive
          atSource atTarget
      _ = coarsePotentialEnergy outer inner configuration resistance (fun vertex => potential (Sum.inl vertex)) :=
        (coarsePotentialEnergy_eq_network_energy outer inner configuration resistance _).symm
      _ ≤ _ := coarsePotentialEnergy_le_substituted_energy outer inner configuration resistance positive potential

theorem substitutedNetwork_resistance
    (outer : Universality.FiniteNetwork outerVertices outerEdges)
    (inner : Universality.FiniteNetwork innerVertices innerEdges)
    (configuration : Fin outerEdges → Universality.FiniteNetwork.Configuration innerEdges)
    (crosses : outer.crosses (inner.coarseConfiguration configuration) = true)
    (resistance : (Σ edge : Fin outerEdges, {child : Fin innerEdges // configuration edge child = true}) → ℝ)
    (positive : ∀ edge, 0 < resistance edge) :
    (substitutedNetwork outer inner configuration).effectiveResistance resistance =
      (network outer (inner.coarseConfiguration configuration)).effectiveResistance
        (coarseResistance inner configuration resistance) := by
  have conductanceEquality := substitutedNetwork_conductance outer inner configuration resistance positive
  rw [(substitutedNetwork outer inner configuration).effectiveConductance_eq_reciprocalResistance
      (substitutedNetwork_connected outer inner configuration crosses) positive,
    (network outer (inner.coarseConfiguration configuration)).effectiveConductance_eq_reciprocalResistance
      (connected_of_crosses outer _ crosses)
      (coarseResistance_positive inner configuration resistance positive)] at conductanceEquality
  exact inv_injective (by simpa only [one_div] using conductanceEquality)

end
end IGSIII34.Percolation
