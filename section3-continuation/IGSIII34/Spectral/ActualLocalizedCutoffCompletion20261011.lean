import IGSIII34.Spectral.ActualSocketCutoffBoundaryCompletion20261011
import IGSIII34.Spectral.PhysicalParentCellCutoffEnergyCompletion20261011
import IGSIII34.Spectral.NoncollarPathSuffixCompletion20261011
import IGSIII34.Percolation.Continuation.NaturalPhysicalOmegaCompletion20261011

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000

namespace IGSIII34.Spectral
noncomputable section
open Universality Universality.FiniteNetwork IGSIII.Chemical.Substitution IGSIII.Geometry
open IGSIII.Probability IGSIII34.Percolation IGSIII34.ResistanceLimit IGSIII34.Forms Resistance
open MeasureTheory Filter
open scoped BigOperators _root_.Topology

/-- The actual noncollar event produces finite-energy physical cutoffs
equal to one at the typical point, with the correct refined-cell energy and
Perron socket mass bounds. No cutoff, localization or energy bound is assumed. -/
theorem actual_localized_cutoff_noncollar_paths_completion20261011
    (rule : Rule) (classicalRule : rule.Classical) (p : ℝ)
    (positive : 0 < p) (belowOne : p < 1) (fixedPoint : rule.network.reliability p = p)
    (natural : NaturalResistanceCompletion20261011 rule p positive belowOne fixedPoint) :
    ∀ᵐ marks ∂independentInnovationLaw rule p positive belowOne fixedPoint,
      ∀ slack : ℝ, 1 < slack → ∃ threshold : ℕ,
      ∀ (typical : StationaryHarmonicTypical rule p positive belowOne fixedPoint natural.growth
          (natural.amplitude • natural.field) marks),
      ∀ (compactness : CompactSpace (UniformSpace.Completion
        (ActualStationaryEnergySkeleton rule p positive belowOne fixedPoint natural.growth
          (natural.amplitude • natural.field) (zero_lt_one.trans natural.aboveOne)
          (harmonicTypicalEnergyMarks rule p positive belowOne fixedPoint natural.growth
            (natural.amplitude • natural.field) ⟨marks, typical⟩)))),
      ∀ (boundaryLaw : Measure (Π depth, Fin depth → (Fin rule.edges × Bool)))
        (probability : IsProbabilityMeasure boundaryLaw)
        (retainedPaths : ∀ᵐ path ∂boundaryLaw, ∀ depth,
          Fin.init (path (depth + 1)) = path depth ∧ retainedComponentState rule marks (List.ofFn (path depth)) ≠ .inactive),
      ∀ (realization : (Π depth, Fin depth → (Fin rule.edges × Bool)) →
        ActualStationaryElectricalSpace rule p positive belowOne fixedPoint natural.growth
          (natural.amplitude • natural.field) (zero_lt_one.trans natural.aboveOne) ⟨marks, typical.1.1⟩)
        (realizationMeasurable : Measurable realization)
        (convergence : ∀ᵐ path ∂boundaryLaw, Tendsto (fun depth =>
          actualElectricalComponentWordPoint rule p positive belowOne fixedPoint natural.growth
            (natural.amplitude • natural.field) (zero_lt_one.trans natural.aboveOne) marks typical.1.1 depth (path (depth + 1)))
          atTop (𝓝 (realization path))),
      ∀ᵐ path ∂boundaryLaw, ∀ coarse fine : ℕ, threshold ≤ coarse + fine + 2 →
        path ∉ terminalCylinderCollarCompletion20261011 rule 0 (coarse + 1) (fine + 1) →
        ∃ potential : actualEnergyDomain rule p positive belowOne fixedPoint natural.growth
          (natural.amplitude • natural.field) (zero_lt_one.trans natural.aboveOne)
          (harmonicTypicalEnergyMarks rule p positive belowOne fixedPoint natural.growth
            (natural.amplitude • natural.field) ⟨marks, typical⟩),
          actualEnergyExtensionLinear rule p positive belowOne fixedPoint natural.growth
            (natural.amplitude • natural.field) (zero_lt_one.trans natural.aboveOne)
            (harmonicTypicalEnergyMarks rule p positive belowOne fixedPoint natural.growth
              (natural.amplitude • natural.field) ⟨marks, typical⟩) potential (realization path) = 1 ∧
          (∀ point, 0 ≤ actualEnergyExtensionLinear rule p positive belowOne fixedPoint natural.growth
            (natural.amplitude • natural.field) (zero_lt_one.trans natural.aboveOne)
            (harmonicTypicalEnergyMarks rule p positive belowOne fixedPoint natural.growth
              (natural.amplitude • natural.field) ⟨marks, typical⟩) potential point ∧
            actualEnergyExtensionLinear rule p positive belowOne fixedPoint natural.growth
              (natural.amplitude • natural.field) (zero_lt_one.trans natural.aboveOne)
              (harmonicTypicalEnergyMarks rule p positive belowOne fixedPoint natural.growth
                (natural.amplitude • natural.field) ⟨marks, typical⟩) potential point ≤ 1) ∧
          limitingEnergy
            (actualEnergyEndpoint rule p positive belowOne fixedPoint natural.growth
              (natural.amplitude • natural.field) (zero_lt_one.trans natural.aboveOne)
              (harmonicTypicalEnergyMarks rule p positive belowOne fixedPoint natural.growth
                (natural.amplitude • natural.field) ⟨marks, typical⟩))
            (actualEnergyConductance rule p positive belowOne fixedPoint natural.growth
              (natural.amplitude • natural.field)
              (harmonicTypicalEnergyMarks rule p positive belowOne fixedPoint natural.growth
                (natural.amplitude • natural.field) ⟨marks, typical⟩)) potential.val ≤
              (rule.edges : ℝ)^(fine + 1) * natural.growth^(coarse + fine + 2) * slack^(coarse + fine + 2) ∧
          (∫ point, actualEnergyExtensionLinear rule p positive belowOne fixedPoint natural.growth
            (natural.amplitude • natural.field) (zero_lt_one.trans natural.aboveOne)
            (harmonicTypicalEnergyMarks rule p positive belowOne fixedPoint natural.growth
              (natural.amplitude • natural.field) ⟨marks, typical⟩) potential point^2 ∂(boundaryLaw.map realization)) ≤
            boundaryLaw.real (physicalSocketCylinderCompletion20261011 rule (coarse + 1)
              (fun index => (path (coarse + 1) index).1)) := by
  classical
  obtain ⟨constant, constantPositive, growthBounds, membership, fixed⟩ :=
    natural_physical_omega_witness_completion20261011 rule classicalRule p positive belowOne fixedPoint natural
  have fieldPositive := electricalOmega_ae_positive rule classicalRule p positive belowOne fixedPoint
    natural.growth (zero_lt_one.trans natural.aboveOne) (fun depth => (growthBounds depth).1)
    (natural.amplitude • natural.field) membership
  have stationary := electricalField_stationary_of_fixed rule p positive belowOne fixedPoint natural.growth
    (zero_lt_one.trans natural.aboveOne) (natural.amplitude • natural.field) fieldPositive fixed
  filter_upwards [stationary, physical_parent_cell_harmonic_cutoff_energy_completion20261011
    rule p positive belowOne fixedPoint natural] with marks stationary energies
  intro slack greater
  obtain ⟨threshold, energies⟩ := energies slack greater
  refine ⟨threshold, ?_⟩
  intro typical compactness boundaryLaw probability retainedPaths realization realizationMeasurable convergence
  letI := compactness
  letI := probability
  have allValues : ∀ᵐ path ∂boundaryLaw, ∀ depth : ℕ,
      ∀ word : Fin (depth + 1) → (Fin rule.edges × Bool), path (depth + 1) = word →
      actualHarmonicCompletionFunctionCompletion20261011 rule p positive belowOne fixedPoint natural.growth
        (natural.amplitude • natural.field) (zero_lt_one.trans natural.aboveOne) ⟨marks, typical⟩ depth
        (fun vertex => if vertex ∈ physicalEdgeRootCutoffVerticesCompletion20261011 rule depth
          (generationWordEdge rule depth (fun index => (word index).1)) then 1 else 0) (realization path) = 1 := by
    apply ae_all_iff.mpr
    intro depth
    apply ae_all_iff.mpr
    intro word
    exact actual_physical_root_cutoff_realization_one_completion20261011 rule p positive belowOne fixedPoint natural.growth
      (natural.amplitude • natural.field) (zero_lt_one.trans natural.aboveOne) ⟨marks, typical⟩ stationary
      boundaryLaw retainedPaths realization convergence depth word
  filter_upwards [allValues, retainedPaths] with path values retained
  intro coarse fine after avoids
  obtain ⟨suffix, decomposition, nonterminal⟩ := actual_noncollar_path_refined_roots_internal_completion20261011
    rule path (fun depth => (retained depth).1) coarse fine avoids
  let selected := physicalEdgeRootCutoffVerticesCompletion20261011 rule (coarse + fine + 1)
    (generationWordEdge rule (coarse + fine + 1) (fun index => (path (coarse + fine + 2) index).1))
  have internal : ∀ vertex ∈ selected, ∃ inside : (rule.generation fine).network.InteriorVertex,
      (generationBlockCellEmbedding rule coarse fine
        (generationWordEdge rule coarse (fun index => (path (coarse + 1) index).1))).vertex inside.val = vertex := by
    dsimp only [selected]
    rw [decomposition, block_word_append_first_coordinates_completion20261011, generation_word_edge_append_completion20261011]
    exact nonterminal_physical_edge_cutoff_roots_parent_interior_completion20261011 rule coarse fine
      (generationWordEdge rule coarse (fun index => (path (coarse + 1) index).1)) (fun index => (suffix index).1) nonterminal
  refine ⟨⟨actualHarmonicFunction rule p positive belowOne fixedPoint natural.growth (natural.amplitude • natural.field)
      (zero_lt_one.trans natural.aboveOne) ⟨marks, typical⟩ (coarse + fine + 1) (fun vertex => if vertex ∈ selected then 1 else 0),
    actualHarmonicFunction_finite rule p positive belowOne fixedPoint natural.growth (natural.amplitude • natural.field)
      (zero_lt_one.trans natural.aboveOne) ⟨marks, typical⟩ (coarse + fine + 1) (fun vertex => if vertex ∈ selected then 1 else 0)⟩,
      values (coarse + fine + 1) (path (coarse + fine + 2)) rfl, ?_, ?_, ?_⟩
  · exact actual_harmonic_completion_unit_interval_completion20261011 rule p positive belowOne fixedPoint natural.growth
      (natural.amplitude • natural.field) (zero_lt_one.trans natural.aboveOne) ⟨marks, typical⟩ stationary
      (coarse + fine + 1) (fun vertex => if vertex ∈ selected then 1 else 0)
      (fun vertex _ => by by_cases member : vertex ∈ selected <;> simp [member])
  · exact energies coarse fine after typical
      (generationWordEdge rule coarse (fun index => (path (coarse + 1) index).1)) selected internal
  · exact actual_parent_binary_cutoff_pushforward_square_integral_completion20261011 rule p positive belowOne fixedPoint natural.growth
      (natural.amplitude • natural.field) (zero_lt_one.trans natural.aboveOne) ⟨marks, typical⟩ stationary boundaryLaw retainedPaths
      realization convergence realizationMeasurable coarse fine (fun index => (path (coarse + 1) index).1) selected internal

end
end IGSIII34.Spectral
