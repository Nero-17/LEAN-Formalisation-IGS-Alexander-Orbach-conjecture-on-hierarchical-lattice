import IGSIII.Geometry.ChemicalMetricMeasureCode
import IGSIII.Geometry.FullComponentMassApproximation
import IGSIII.Geometry.ActualComponentRetainedAnchors
import IGSIII.Chemical.SmallBall.CodedMetricMeasureUniqueness
import IGSIII.Geometry.ChemicalMetricCodeFaithfulness
import IGSIII.Chemical.SmallBall.ActualChemicalTerminals

set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option backward.isDefEq.respectTransparency false

namespace IGSIII.Geometry
noncomputable section

open Universality Universality.FiniteNetwork IGSIII.Chemical.Substitution MeasureTheory Filter
open scoped BigOperators Topology

private instance : MeasurableSpace OrientedState := ⊤
private instance : MeasurableSingletonClass OrientedState := ⟨fun _ => trivial⟩

/-- The actual coarse endpoint used by the boundary projection. Inactive
words name the retained source, just as in the actual word-point map. -/
def chemicalComponentAnchorCode (rule : Rule)
    (marks : (List (Fin rule.edges) × Bool) → Configuration rule.edges)
    (age : ℕ) (word : Fin (age + 1) → (Fin rule.edges × Bool)) : Fin (rule.generation age).vertices :=
  if retainedComponentState rule marks (List.ofFn word) ≠ .inactive then componentWordAnchor rule marks age word
  else (rule.generation age).network.source

theorem chemicalComponentAnchorCode_measurable (rule : Rule) (age : ℕ)
    (word : Fin (age + 1) → (Fin rule.edges × Bool)) :
    Measurable (fun marks => chemicalComponentAnchorCode rule marks age word) := by
  exact (measurable_of_countable (fun state : OrientedState =>
    if state ≠ .inactive then
      if state.sourceSelected then
        ((rule.generation age).network.endpoint (generationWordEdge rule age (fun index => (word index).1))).1
      else ((rule.generation age).network.endpoint (generationWordEdge rule age (fun index => (word index).1))).2
    else (rule.generation age).network.source)).comp
      (retainedComponentStateFrom_measurable rule [] .connected (List.ofFn word))

def ChemicalMarkedMetricMeasureCode (rule : Rule) :=
  ChemicalMetricMeasureCode rule × (∀ age, (Fin (age + 1) → (Fin rule.edges × Bool)) → Fin (rule.generation age).vertices)

instance chemicalMarkedMetricMeasureCodeMeasurableSpace (rule : Rule) : MeasurableSpace (ChemicalMarkedMetricMeasureCode rule) :=
  inferInstanceAs (MeasurableSpace (ChemicalMetricMeasureCode rule ×
    (∀ age, (Fin (age + 1) → (Fin rule.edges × Bool)) → Fin (rule.generation age).vertices)))

def chemicalMarkedMetricMeasureCode (rule : Rule) (p : ℝ) (positive : 0 < p) (belowOne : p < 1)
    (fixedPoint : rule.network.reliability p = p) (growth amplitude : ℝ)
    (value : Lp ℝ 2 (independentInnovationLaw rule p positive belowOne fixedPoint))
    (marks : (List (Fin rule.edges) × Bool) → Configuration rule.edges) : ChemicalMarkedMetricMeasureCode rule :=
  ⟨chemicalMetricMeasureCode rule p positive belowOne fixedPoint growth amplitude value marks,
    chemicalComponentAnchorCode rule marks⟩

theorem chemicalMarkedMetricMeasureCode_measurable (rule : Rule) (p : ℝ) (positive : 0 < p) (belowOne : p < 1)
    (fixedPoint : rule.network.reliability p = p) (growth amplitude : ℝ)
    (value : Lp ℝ 2 (independentInnovationLaw rule p positive belowOne fixedPoint)) :
    Measurable (chemicalMarkedMetricMeasureCode rule p positive belowOne fixedPoint growth amplitude value) :=
  (chemicalMetricMeasureCode_measurable rule p positive belowOne fixedPoint growth amplitude value).prodMk
    (measurable_pi_lambda _ (fun age => measurable_pi_lambda _ (chemicalComponentAnchorCode_measurable rule age)))

theorem chemicalComponentAnchorCode_eq_retained_anchor (rule : Rule)
    (marks : (List (Fin rule.edges) × Bool) → Configuration rule.edges)
    (crossing : ∀ address opened, rule.network.crosses (marks (address, opened)) = opened)
    (age : ℕ) (word : Fin (age + 1) → (Fin rule.edges × Bool)) :
    chemicalComponentAnchorCode rule marks age word = (actualComponentRetainedAnchor rule marks crossing age word).val := by
  unfold chemicalComponentAnchorCode actualComponentRetainedAnchor
  split <;> rfl

theorem actualComponentWordPoint_eq_code_label
    (rule : Rule) (classicalRule : rule.Classical)
    (marks : (List (Fin rule.edges) × Bool) → Configuration rule.edges)
    (crossing : ∀ address opened, rule.network.crosses (marks (address, opened)) = opened)
    (coherent : configurationSequenceCoherent rule (fun depth => markedGenerationConfiguration rule marks depth [] true))
    (scale : ℝ) (scalePositive : 0 < scale)
    (lengths : ∀ depth, Fin (rule.generation depth).edges → ℝ)
    (nonnegative : ∀ depth edge, 0 ≤ lengths depth edge)
    (positive : ∀ depth edge, markedGenerationConfiguration rule marks depth [] true edge = true → 0 < lengths depth edge)
    (childConvergence : ∀ coarse edge, Tendsto (fun fine =>
      (((rule.generation fine).network.openGraph
        (generationBlockCells rule coarse fine (markedGenerationConfiguration rule marks (coarse + fine + 1) [] true) edge)).dist
          (rule.generation fine).network.source (rule.generation fine).network.target : ℝ) /
        scale ^ (coarse + fine + 2)) atTop (𝓝 (lengths coarse edge)))
    (age : ℕ) (word : Fin (age + 1) → (Fin rule.edges × Bool)) :
    actualComponentWordPoint rule classicalRule marks crossing coherent scale scalePositive lengths nonnegative positive childConvergence age word =
      actualChemicalLabelPoint rule classicalRule (fun depth => markedGenerationConfiguration rule marks depth [] true)
        coherent scale scalePositive lengths nonnegative positive childConvergence ⟨age, chemicalComponentAnchorCode rule marks age word⟩ := by
  rw [chemicalComponentAnchorCode_eq_retained_anchor rule marks crossing age word,
    actualChemicalLabelPoint_of_retained]
  exact actualComponentWordPoint_eq_retained_anchor rule classicalRule marks crossing coherent scale scalePositive
    lengths nonnegative positive childConvergence age word

/-- Actual counting convergence identifies the measurable cylinder code with
the weights of the already constructed boundary probability. -/
theorem chemicalCylinderMassCode_boundary_weights
    (rule : Rule) (marks : (List (Fin rule.edges) × Bool) → Configuration rule.edges)
    (weight : List (Fin rule.edges × Bool) → ℝ) (nonnegative : ∀ address, 0 ≤ weight address)
    (convergence : ∀ address, Tendsto (fun fine => markedComponentVertexMass rule marks fine address /
      markedComponentVertexMass rule marks (fine + address.length) []) atTop (𝓝 (weight address)))
    (boundary : Measure (Π depth, Fin depth → (Fin rule.edges × Bool))) [IsProbabilityMeasure boundary]
    (atoms : ∀ age word, boundary {path | path age = word} = ENNReal.ofReal (weight (List.ofFn word))) :
    (∀ address, 0 ≤ chemicalCylinderMassCode rule marks address) ∧
    (∀ age, ∑ word : Fin age → (Fin rule.edges × Bool), chemicalCylinderMassCode rule marks (List.ofFn word) = 1) := by
  have identification : chemicalCylinderMassCode rule marks = weight :=
    funext (fun address => chemicalCylinderMassCode_eq_limit rule marks address (weight address) (convergence address))
  rw [identification]
  exact ⟨nonnegative, probability_boundary_weights_sum weight nonnegative boundary atoms⟩

def chemicalCylinderAtomicProjection (rule : Rule)
    (marks : (List (Fin rule.edges) × Bool) → Configuration rule.edges)
    {Space : Type*} [MeasurableSpace Space] (age : ℕ)
    (nonnegative : ∀ word : Fin age → (Fin rule.edges × Bool), 0 ≤ chemicalCylinderMassCode rule marks (List.ofFn word))
    (massOne : ∑ word : Fin age → (Fin rule.edges × Bool), chemicalCylinderMassCode rule marks (List.ofFn word) = 1)
    (anchor : (Fin age → (Fin rule.edges × Bool)) → Space) : Measure Space :=
  (finiteWeightPMF (fun word => chemicalCylinderMassCode rule marks (List.ofFn word)) nonnegative massOne).toMeasure.map anchor

/-- The code's finite atomic projection is exactly the actual boundary word
marginal at the chosen anchors. No independently chosen random measure enters. -/
theorem chemicalCylinderAtomicProjection_eq_boundary
    (rule : Rule) (marks : (List (Fin rule.edges) × Bool) → Configuration rule.edges)
    (weight : List (Fin rule.edges × Bool) → ℝ)
    (convergence : ∀ address, Tendsto (fun fine => markedComponentVertexMass rule marks fine address /
      markedComponentVertexMass rule marks (fine + address.length) []) atTop (𝓝 (weight address)))
    (boundary : Measure (Π depth, Fin depth → (Fin rule.edges × Bool)))
    (atoms : ∀ age word, boundary {path | path age = word} = ENNReal.ofReal (weight (List.ofFn word)))
    {Space : Type*} [MeasurableSpace Space] (age : ℕ)
    (nonnegative : ∀ word : Fin age → (Fin rule.edges × Bool), 0 ≤ chemicalCylinderMassCode rule marks (List.ofFn word))
    (massOne : ∑ word : Fin age → (Fin rule.edges × Bool), chemicalCylinderMassCode rule marks (List.ofFn word) = 1)
    (anchor : (Fin age → (Fin rule.edges × Bool)) → Space) :
    chemicalCylinderAtomicProjection rule marks age nonnegative massOne anchor = boundary.map (fun path => anchor (path age)) := by
  have marginal : boundary.map (fun path => path age) =
      (finiteWeightPMF (fun word : Fin age → (Fin rule.edges × Bool) => chemicalCylinderMassCode rule marks (List.ofFn word))
        nonnegative massOne).toMeasure := by
    apply Measure.ext_of_singleton
    intro word
    rw [Measure.map_apply (measurable_pi_apply age) (measurableSet_singleton word), finiteWeightPMF_singleton]
    change boundary {path | path age = word} = _
    rw [atoms,
      chemicalCylinderMassCode_eq_limit rule marks (List.ofFn word) (weight (List.ofFn word)) (convergence _)]
  unfold chemicalCylinderAtomicProjection
  rw [← marginal, Measure.map_map (measurable_of_finite anchor) (measurable_pi_apply age)]
  rfl

/-- Identical coded cylinder weights and matching anchors give identical
finite atomic measures after the actual metric identification. -/
theorem chemicalCylinderAtomicProjection_map_eq
    (rule : Rule)
    (firstMarks lastMarks : (List (Fin rule.edges) × Bool) → Configuration rule.edges)
    (codes : chemicalCylinderMassCode rule firstMarks = chemicalCylinderMassCode rule lastMarks)
    {First Last : Type*} [MeasurableSpace First] [MeasurableSpace Last]
    (map : First → Last) (mapMeasurable : Measurable map) (age : ℕ)
    (firstNonnegative : ∀ word : Fin age → (Fin rule.edges × Bool), 0 ≤ chemicalCylinderMassCode rule firstMarks (List.ofFn word))
    (lastNonnegative : ∀ word : Fin age → (Fin rule.edges × Bool), 0 ≤ chemicalCylinderMassCode rule lastMarks (List.ofFn word))
    (firstMassOne : ∑ word : Fin age → (Fin rule.edges × Bool), chemicalCylinderMassCode rule firstMarks (List.ofFn word) = 1)
    (lastMassOne : ∑ word : Fin age → (Fin rule.edges × Bool), chemicalCylinderMassCode rule lastMarks (List.ofFn word) = 1)
    (firstAnchor : (Fin age → (Fin rule.edges × Bool)) → First)
    (lastAnchor : (Fin age → (Fin rule.edges × Bool)) → Last)
    (anchors : ∀ word, map (firstAnchor word) = lastAnchor word) :
    (chemicalCylinderAtomicProjection rule firstMarks age firstNonnegative firstMassOne firstAnchor).map map =
      chemicalCylinderAtomicProjection rule lastMarks age lastNonnegative lastMassOne lastAnchor := by
  unfold chemicalCylinderAtomicProjection
  rw [Measure.map_map mapMeasurable (measurable_of_finite firstAnchor)]
  have weights : (finiteWeightPMF (fun word : Fin age → (Fin rule.edges × Bool) => chemicalCylinderMassCode rule firstMarks (List.ofFn word))
      firstNonnegative firstMassOne).toMeasure =
      (finiteWeightPMF (fun word : Fin age → (Fin rule.edges × Bool) => chemicalCylinderMassCode rule lastMarks (List.ofFn word))
        lastNonnegative lastMassOne).toMeasure := by
    apply Measure.ext_of_singleton
    intro word
    simp only [finiteWeightPMF_singleton, codes]
  rw [weights]
  congr 1
  funext word
  exact anchors word

/-- Equality of the actual coded weights preserves the limiting probability
measure whenever the metric identification matches the finite word anchors. -/
theorem boundary_measure_map_eq_of_chemicalCylinderMassCode
    (rule : Rule)
    (firstMarks lastMarks : (List (Fin rule.edges) × Bool) → Configuration rule.edges)
    (codes : chemicalCylinderMassCode rule firstMarks = chemicalCylinderMassCode rule lastMarks)
    (firstWeight lastWeight : List (Fin rule.edges × Bool) → ℝ)
    (firstNonnegative : ∀ address, 0 ≤ firstWeight address)
    (lastNonnegative : ∀ address, 0 ≤ lastWeight address)
    (firstCounts : ∀ address, Tendsto (fun fine => markedComponentVertexMass rule firstMarks fine address /
      markedComponentVertexMass rule firstMarks (fine + address.length) []) atTop (𝓝 (firstWeight address)))
    (lastCounts : ∀ address, Tendsto (fun fine => markedComponentVertexMass rule lastMarks fine address /
      markedComponentVertexMass rule lastMarks (fine + address.length) []) atTop (𝓝 (lastWeight address)))
    (firstBoundary lastBoundary : Measure (Π depth, Fin depth → (Fin rule.edges × Bool)))
    [IsProbabilityMeasure firstBoundary] [IsProbabilityMeasure lastBoundary]
    (firstAtoms : ∀ age word, firstBoundary {path | path age = word} = ENNReal.ofReal (firstWeight (List.ofFn word)))
    (lastAtoms : ∀ age word, lastBoundary {path | path age = word} = ENNReal.ofReal (lastWeight (List.ofFn word)))
    {First Last : Type*} [MetricSpace First] [MetricSpace Last]
    [MeasurableSpace First] [MeasurableSpace Last] [BorelSpace First] [BorelSpace Last]
    (equivalence : First ≃ᵢ Last)
    (firstAnchor : ∀ age, (Fin (age + 1) → (Fin rule.edges × Bool)) → First)
    (lastAnchor : ∀ age, (Fin (age + 1) → (Fin rule.edges × Bool)) → Last)
    (anchors : ∀ age word, equivalence (firstAnchor age word) = lastAnchor age word)
    (firstRealization : (Π depth, Fin depth → (Fin rule.edges × Bool)) → First)
    (lastRealization : (Π depth, Fin depth → (Fin rule.edges × Bool)) → Last)
    (firstMeasurable : Measurable firstRealization) (lastMeasurable : Measurable lastRealization)
    (firstConvergence : Tendsto (fun age => levyProkhorovEDist
      (firstBoundary.map (fun path => firstAnchor age (path (age + 1))))
      (firstBoundary.map firstRealization)) atTop (𝓝 0))
    (lastConvergence : Tendsto (fun age => levyProkhorovEDist
      (lastBoundary.map (fun path => lastAnchor age (path (age + 1))))
      (lastBoundary.map lastRealization)) atTop (𝓝 0)) :
    (firstBoundary.map firstRealization).map equivalence = lastBoundary.map lastRealization := by
  letI := Measure.isProbabilityMeasure_map firstMeasurable.aemeasurable (μ := firstBoundary)
  letI := Measure.isProbabilityMeasure_map lastMeasurable.aemeasurable (μ := lastBoundary)
  have firstProperties := chemicalCylinderMassCode_boundary_weights rule firstMarks firstWeight firstNonnegative firstCounts firstBoundary firstAtoms
  have lastProperties := chemicalCylinderMassCode_boundary_weights rule lastMarks lastWeight lastNonnegative lastCounts lastBoundary lastAtoms
  apply isometryEquiv_map_measure_eq_of_atomic_approximations equivalence
    (firstBoundary.map firstRealization) (lastBoundary.map lastRealization)
    (fun age => firstBoundary.map (fun path => firstAnchor age (path (age + 1))))
    (fun age => lastBoundary.map (fun path => lastAnchor age (path (age + 1)))) _ firstConvergence lastConvergence
  intro age
  rw [← chemicalCylinderAtomicProjection_eq_boundary rule firstMarks firstWeight firstCounts firstBoundary firstAtoms (age + 1)
      (fun word => firstProperties.1 _) (firstProperties.2 (age + 1)) (firstAnchor age),
    ← chemicalCylinderAtomicProjection_eq_boundary rule lastMarks lastWeight lastCounts lastBoundary lastAtoms (age + 1)
      (fun word => lastProperties.1 _) (lastProperties.2 (age + 1)) (lastAnchor age)]
  exact chemicalCylinderAtomicProjection_map_eq rule firstMarks lastMarks codes equivalence equivalence.continuous.measurable
    (age + 1) (fun word => firstProperties.1 _) (fun word => lastProperties.1 _)
    (firstProperties.2 (age + 1)) (lastProperties.2 (age + 1)) (firstAnchor age) (lastAnchor age) (anchors age)

section ActualFaithfulness

variable (rule : Rule) (classicalRule : rule.Classical)
variable (p : ℝ) (probabilityPositive : 0 < p) (belowOne : p < 1) (fixedPoint : rule.network.reliability p = p)
variable (growth amplitude : ℝ) (growthPositive : 0 < growth)
variable (value : Lp ℝ 2 (independentInnovationLaw rule p probabilityPositive belowOne fixedPoint))
variable (marks lastMarks : (List (Fin rule.edges) × Bool) → Configuration rule.edges)
variable (crossing : ∀ address opened, rule.network.crosses (marks (address, opened)) = opened)
variable (lastCrossing : ∀ address opened, rule.network.crosses (lastMarks (address, opened)) = opened)
variable (coherent : configurationSequenceCoherent rule (fun depth => markedGenerationConfiguration rule marks depth [] true))
variable (lastCoherent : configurationSequenceCoherent rule (fun depth => markedGenerationConfiguration rule lastMarks depth [] true))
variable (nonnegative : ∀ depth edge, 0 ≤ chemicalBlockLimitLength rule p probabilityPositive belowOne fixedPoint growth amplitude value marks depth edge)
variable (lastNonnegative : ∀ depth edge, 0 ≤ chemicalBlockLimitLength rule p probabilityPositive belowOne fixedPoint growth amplitude value lastMarks depth edge)
variable (positive : ∀ depth edge, markedGenerationConfiguration rule marks depth [] true edge = true →
  0 < chemicalBlockLimitLength rule p probabilityPositive belowOne fixedPoint growth amplitude value marks depth edge)
variable (lastPositive : ∀ depth edge, markedGenerationConfiguration rule lastMarks depth [] true edge = true →
  0 < chemicalBlockLimitLength rule p probabilityPositive belowOne fixedPoint growth amplitude value lastMarks depth edge)
variable (childConvergence : ∀ coarse edge, Tendsto (fun fine =>
  (((rule.generation fine).network.openGraph
    (generationBlockCells rule coarse fine (markedGenerationConfiguration rule marks (coarse + fine + 1) [] true) edge)).dist
      (rule.generation fine).network.source (rule.generation fine).network.target : ℝ) /
    growth ^ (coarse + fine + 2)) atTop
      (𝓝 (chemicalBlockLimitLength rule p probabilityPositive belowOne fixedPoint growth amplitude value marks coarse edge)))
variable (lastConvergence : ∀ coarse edge, Tendsto (fun fine =>
  (((rule.generation fine).network.openGraph
    (generationBlockCells rule coarse fine (markedGenerationConfiguration rule lastMarks (coarse + fine + 1) [] true) edge)).dist
      (rule.generation fine).network.source (rule.generation fine).network.target : ℝ) /
    growth ^ (coarse + fine + 2)) atTop
      (𝓝 (chemicalBlockLimitLength rule p probabilityPositive belowOne fixedPoint growth amplitude value lastMarks coarse edge)))

/-- The enriched measurable code determines the actual completed cluster,
its boundary probability, and its two ordered terminals up to one measure
preserving isometry. All metric and measure identities are recovered from
the actual code and the previously proved counting and projection limits. -/
theorem exists_actual_marked_measure_isometryEquiv_of_code_eq
    (codeEquality : chemicalMarkedMetricMeasureCode rule p probabilityPositive belowOne fixedPoint growth amplitude value marks =
      chemicalMarkedMetricMeasureCode rule p probabilityPositive belowOne fixedPoint growth amplitude value lastMarks)
    (weight lastWeight : List (Fin rule.edges × Bool) → ℝ)
    (weightNonnegative : ∀ address, 0 ≤ weight address) (lastWeightNonnegative : ∀ address, 0 ≤ lastWeight address)
    (counts : ∀ address, Tendsto (fun fine => markedComponentVertexMass rule marks fine address /
      markedComponentVertexMass rule marks (fine + address.length) []) atTop (𝓝 (weight address)))
    (lastCounts : ∀ address, Tendsto (fun fine => markedComponentVertexMass rule lastMarks fine address /
      markedComponentVertexMass rule lastMarks (fine + address.length) []) atTop (𝓝 (lastWeight address)))
    (boundary lastBoundary : Measure (Π depth, Fin depth → (Fin rule.edges × Bool)))
    [IsProbabilityMeasure boundary] [IsProbabilityMeasure lastBoundary]
    (atoms : ∀ age word, boundary {path | path age = word} = ENNReal.ofReal (weight (List.ofFn word)))
    (lastAtoms : ∀ age word, lastBoundary {path | path age = word} = ENNReal.ofReal (lastWeight (List.ofFn word)))
    (realization : (Π depth, Fin depth → (Fin rule.edges × Bool)) →
      ActualChemicalSpace rule classicalRule (fun depth => markedGenerationConfiguration rule marks depth [] true) coherent growth growthPositive
        (chemicalBlockLimitLength rule p probabilityPositive belowOne fixedPoint growth amplitude value marks)
        nonnegative positive childConvergence)
    (lastRealization : (Π depth, Fin depth → (Fin rule.edges × Bool)) →
      ActualChemicalSpace rule classicalRule (fun depth => markedGenerationConfiguration rule lastMarks depth [] true) lastCoherent growth growthPositive
        (chemicalBlockLimitLength rule p probabilityPositive belowOne fixedPoint growth amplitude value lastMarks)
        lastNonnegative lastPositive lastConvergence)
    (realizationMeasurable : Measurable realization) (lastRealizationMeasurable : Measurable lastRealization)
    (projectionConvergence : Tendsto (fun age => levyProkhorovEDist
      (boundary.map (fun path => actualComponentWordPoint rule classicalRule marks crossing coherent growth growthPositive
        (chemicalBlockLimitLength rule p probabilityPositive belowOne fixedPoint growth amplitude value marks)
        nonnegative positive childConvergence age (path (age + 1)))) (boundary.map realization)) atTop (𝓝 0))
    (lastProjectionConvergence : Tendsto (fun age => levyProkhorovEDist
      (lastBoundary.map (fun path => actualComponentWordPoint rule classicalRule lastMarks lastCrossing lastCoherent growth growthPositive
        (chemicalBlockLimitLength rule p probabilityPositive belowOne fixedPoint growth amplitude value lastMarks)
        lastNonnegative lastPositive lastConvergence age (path (age + 1)))) (lastBoundary.map lastRealization)) atTop (𝓝 0)) :
    ∃ equivalence : ActualChemicalSpace rule classicalRule (fun depth => markedGenerationConfiguration rule marks depth [] true) coherent growth growthPositive
        (chemicalBlockLimitLength rule p probabilityPositive belowOne fixedPoint growth amplitude value marks)
        nonnegative positive childConvergence ≃ᵢ
      ActualChemicalSpace rule classicalRule (fun depth => markedGenerationConfiguration rule lastMarks depth [] true) lastCoherent growth growthPositive
        (chemicalBlockLimitLength rule p probabilityPositive belowOne fixedPoint growth amplitude value lastMarks)
        lastNonnegative lastPositive lastConvergence,
      (∀ label : ChemicalVertexLabel rule, equivalence
        (actualChemicalLabelPoint rule classicalRule (fun depth => markedGenerationConfiguration rule marks depth [] true) coherent growth growthPositive
          (chemicalBlockLimitLength rule p probabilityPositive belowOne fixedPoint growth amplitude value marks) nonnegative positive childConvergence label) =
        actualChemicalLabelPoint rule classicalRule (fun depth => markedGenerationConfiguration rule lastMarks depth [] true) lastCoherent growth growthPositive
          (chemicalBlockLimitLength rule p probabilityPositive belowOne fixedPoint growth amplitude value lastMarks) lastNonnegative lastPositive lastConvergence label) ∧
      (boundary.map realization).map equivalence = lastBoundary.map lastRealization ∧
      ∀ side, equivalence
        (IGSIII.Chemical.SmallBall.actualChemicalTerminal rule classicalRule (fun depth => markedGenerationConfiguration rule marks depth [] true)
          coherent (fun depth => markedGenerationConfiguration_crosses rule marks crossing depth [] true) growth growthPositive
          (chemicalBlockLimitLength rule p probabilityPositive belowOne fixedPoint growth amplitude value marks) nonnegative positive childConvergence side) =
        IGSIII.Chemical.SmallBall.actualChemicalTerminal rule classicalRule (fun depth => markedGenerationConfiguration rule lastMarks depth [] true)
          lastCoherent (fun depth => markedGenerationConfiguration_crosses rule lastMarks lastCrossing depth [] true) growth growthPositive
          (chemicalBlockLimitLength rule p probabilityPositive belowOne fixedPoint growth amplitude value lastMarks) lastNonnegative lastPositive lastConvergence side := by
  have metricCodes := congrArg (fun code : ChemicalMarkedMetricMeasureCode rule => code.1.1) codeEquality
  have massCodes := congrArg (fun code : ChemicalMarkedMetricMeasureCode rule => code.1.2) codeEquality
  have anchorCodes := congrArg (fun code : ChemicalMarkedMetricMeasureCode rule => code.2) codeEquality
  obtain ⟨equivalence, labels⟩ := exists_actualChemicalLabelIsometryEquiv_of_code_eq rule classicalRule p probabilityPositive belowOne fixedPoint
    growth amplitude growthPositive value marks coherent nonnegative positive childConvergence
    lastMarks lastCoherent lastNonnegative lastPositive lastConvergence metricCodes
  have anchors : ∀ age word, equivalence
      (actualComponentWordPoint rule classicalRule marks crossing coherent growth growthPositive
        (chemicalBlockLimitLength rule p probabilityPositive belowOne fixedPoint growth amplitude value marks) nonnegative positive childConvergence age word) =
      actualComponentWordPoint rule classicalRule lastMarks lastCrossing lastCoherent growth growthPositive
        (chemicalBlockLimitLength rule p probabilityPositive belowOne fixedPoint growth amplitude value lastMarks) lastNonnegative lastPositive lastConvergence age word := by
    intro age word
    rw [actualComponentWordPoint_eq_code_label, actualComponentWordPoint_eq_code_label]
    have equality := labels ⟨age, chemicalComponentAnchorCode rule marks age word⟩
    change chemicalComponentAnchorCode rule marks = chemicalComponentAnchorCode rule lastMarks at anchorCodes
    simpa only [anchorCodes] using equality
  refine ⟨equivalence, labels, ?_, ?_⟩
  · exact boundary_measure_map_eq_of_chemicalCylinderMassCode rule marks lastMarks massCodes weight lastWeight weightNonnegative lastWeightNonnegative
      counts lastCounts boundary lastBoundary atoms lastAtoms equivalence
      (actualComponentWordPoint rule classicalRule marks crossing coherent growth growthPositive
        (chemicalBlockLimitLength rule p probabilityPositive belowOne fixedPoint growth amplitude value marks) nonnegative positive childConvergence)
      (actualComponentWordPoint rule classicalRule lastMarks lastCrossing lastCoherent growth growthPositive
        (chemicalBlockLimitLength rule p probabilityPositive belowOne fixedPoint growth amplitude value lastMarks) lastNonnegative lastPositive lastConvergence)
      anchors realization lastRealization realizationMeasurable lastRealizationMeasurable projectionConvergence lastProjectionConvergence
  · intro side
    have identity := labels ⟨0, plantedVertex (rule.generation 0).network side⟩
    have firstIdentity := actualChemicalLabelPoint_of_retained rule classicalRule
      (fun depth => markedGenerationConfiguration rule marks depth [] true) coherent growth growthPositive
      (chemicalBlockLimitLength rule p probabilityPositive belowOne fixedPoint growth amplitude value marks) nonnegative positive childConvergence 0
      (IGSIII.Chemical.SmallBall.retainedTerminalVertex rule (fun depth => markedGenerationConfiguration rule marks depth [] true)
        (fun depth => markedGenerationConfiguration_crosses rule marks crossing depth [] true) 0 side)
    have lastIdentity := actualChemicalLabelPoint_of_retained rule classicalRule
      (fun depth => markedGenerationConfiguration rule lastMarks depth [] true) lastCoherent growth growthPositive
      (chemicalBlockLimitLength rule p probabilityPositive belowOne fixedPoint growth amplitude value lastMarks) lastNonnegative lastPositive lastConvergence 0
      (IGSIII.Chemical.SmallBall.retainedTerminalVertex rule (fun depth => markedGenerationConfiguration rule lastMarks depth [] true)
        (fun depth => markedGenerationConfiguration_crosses rule lastMarks lastCrossing depth [] true) 0 side)
    simp only [IGSIII.Chemical.SmallBall.retainedTerminalVertex_val] at firstIdentity lastIdentity
    rw [firstIdentity, lastIdentity] at identity
    simpa only [IGSIII.Chemical.SmallBall.actualChemicalTerminal] using identity

end ActualFaithfulness

end
end IGSIII.Geometry
