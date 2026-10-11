import IGSIII34.Percolation.Continuation.ElectricalLawIteration
import IGSIII.Probability.IndependentSubfamilies

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
namespace IGSIII34.Percolation
noncomputable section
open Universality Universality.FiniteNetwork MeasureTheory ProbabilityTheory
open IGSIII.Probability IGSIII.Chemical.Substitution
open scoped ENNReal NNReal

def electricalBoundaryInnovationLaw (rule : Rule) (p : ℝ) (positive : 0 < p) (belowOne : p < 1)
    (fixedPoint : rule.network.reliability p = p) (law : ProbabilityMeasure ℝ≥0) :
    Measure ((List (Fin rule.edges) × Bool) → Configuration rule.edges × ℝ≥0) :=
  Measure.infinitePi (fun coordinate : List (Fin rule.edges) × Bool =>
    (Rule.ConfigurationHistory.law rule p positive belowOne fixedPoint coordinate.2 0).prod (law : Measure ℝ≥0))

instance electricalBoundaryInnovationLaw_probability (rule : Rule) (p : ℝ) (positive : 0 < p) (belowOne : p < 1)
    (fixedPoint : rule.network.reliability p = p) (law : ProbabilityMeasure ℝ≥0) :
    IsProbabilityMeasure (electricalBoundaryInnovationLaw rule p positive belowOne fixedPoint law) := by
  letI : ∀ coordinate : List (Fin rule.edges) × Bool,
      IsProbabilityMeasure (Rule.ConfigurationHistory.law rule p positive belowOne fixedPoint coordinate.2 0) :=
    fun coordinate => Rule.ConfigurationHistory.law_probability rule p positive belowOne fixedPoint coordinate.2 0
  unfold electricalBoundaryInnovationLaw
  infer_instance

def electricalBoundaryTreeShift (rule : Rule) (address : List (Fin rule.edges))
    (sample : (List (Fin rule.edges) × Bool) → Configuration rule.edges × ℝ≥0) :
    (List (Fin rule.edges) × Bool) → Configuration rule.edges × ℝ≥0 :=
  fun coordinate => sample (address++coordinate.1, coordinate.2)

theorem electricalBoundaryTreeShift_measurable (rule : Rule) (address : List (Fin rule.edges)) :
    Measurable (electricalBoundaryTreeShift rule address) :=
  measurable_pi_lambda _ (fun coordinate => measurable_pi_apply (address++coordinate.1, coordinate.2))

private theorem electricalBoundaryChildCoordinate_injective (rule : Rule) : Function.Injective
    (fun coordinate : (edge : Fin rule.edges) × (List (Fin rule.edges) × Bool) =>
      (coordinate.1::coordinate.2.1, coordinate.2.2)) := by
  rintro ⟨firstEdge, firstAddress, firstState⟩ ⟨secondEdge, secondAddress, secondState⟩ equality
  have addresses := congrArg Prod.fst equality
  have states := congrArg Prod.snd equality
  have parts := List.cons.inj addresses
  cases parts.1
  cases parts.2
  cases states
  rfl

theorem electricalBoundaryTreeChildren_map (rule : Rule) (p : ℝ) (positive : 0 < p)
    (belowOne : p < 1) (fixedPoint : rule.network.reliability p = p) (law : ProbabilityMeasure ℝ≥0) :
    (electricalBoundaryInnovationLaw rule p positive belowOne fixedPoint law).map
      (fun sample edge => electricalBoundaryTreeShift rule [edge] sample) =
      Measure.infinitePi (fun _ : Fin rule.edges => electricalBoundaryInnovationLaw rule p positive belowOne fixedPoint law) := by
  letI : ∀ coordinate : List (Fin rule.edges) × Bool,
      IsProbabilityMeasure (Rule.ConfigurationHistory.law rule p positive belowOne fixedPoint coordinate.2 0) :=
    fun coordinate => Rule.ConfigurationHistory.law_probability rule p positive belowOne fixedPoint coordinate.2 0
  exact infinitePi_subfamilies_map
    (fun coordinate : List (Fin rule.edges) × Bool =>
      (Rule.ConfigurationHistory.law rule p positive belowOne fixedPoint coordinate.2 0).prod (law : Measure ℝ≥0))
    (fun coordinate : (edge : Fin rule.edges) × (List (Fin rule.edges) × Bool) =>
      (coordinate.1::coordinate.2.1, coordinate.2.2)) (electricalBoundaryChildCoordinate_injective rule)

private def electricalBoundaryRootTailIndex (rule : Rule) : Bool → Type
  | false => Bool
  | true => Fin rule.edges × (List (Fin rule.edges) × Bool)

private def electricalBoundaryRootTailCoordinate (rule : Rule) :
    ((group : Bool) × electricalBoundaryRootTailIndex rule group) → List (Fin rule.edges) × Bool
  | ⟨false, opened⟩ => ([], opened)
  | ⟨true, edge, address, opened⟩ => (edge::address, opened)

private theorem electricalBoundaryRootTailCoordinate_injective (rule : Rule) :
    Function.Injective (electricalBoundaryRootTailCoordinate rule) := by
  rintro ⟨firstGroup, first⟩ ⟨secondGroup, second⟩ equality
  cases firstGroup <;> cases secondGroup
  · have states := congrArg Prod.snd equality
    cases states
    rfl
  · have addresses := congrArg Prod.fst equality
    cases addresses
  · have addresses := congrArg Prod.fst equality
    cases addresses
  · rcases first with ⟨firstEdge, firstAddress, firstState⟩
    rcases second with ⟨secondEdge, secondAddress, secondState⟩
    have addresses := congrArg Prod.fst equality
    have states := congrArg Prod.snd equality
    have parts := List.cons.inj addresses
    cases parts.1
    cases parts.2
    cases states
    rfl

theorem electricalBoundaryTreeRoot_children_map (rule : Rule) (p : ℝ) (positive : 0 < p)
    (belowOne : p < 1) (fixedPoint : rule.network.reliability p = p) (law : ProbabilityMeasure ℝ≥0) :
    (electricalBoundaryInnovationLaw rule p positive belowOne fixedPoint law).map
      (fun sample => ((sample ([], true)).1, fun edge => electricalBoundaryTreeShift rule [edge] sample)) =
      (connectedConfigurationLaw rule p positive belowOne fixedPoint : Measure (Configuration rule.edges)).prod
        (Measure.infinitePi (fun _ : Fin rule.edges => electricalBoundaryInnovationLaw rule p positive belowOne fixedPoint law)) := by
  letI : ∀ coordinate : List (Fin rule.edges) × Bool,
      IsProbabilityMeasure (Rule.ConfigurationHistory.law rule p positive belowOne fixedPoint coordinate.2 0) :=
    fun coordinate => Rule.ConfigurationHistory.law_probability rule p positive belowOne fixedPoint coordinate.2 0
  have independent := infinitePi_subfamilies_independent
    (fun coordinate : List (Fin rule.edges) × Bool =>
      (Rule.ConfigurationHistory.law rule p positive belowOne fixedPoint coordinate.2 0).prod (law : Measure ℝ≥0))
    (electricalBoundaryRootTailCoordinate rule) (electricalBoundaryRootTailCoordinate_injective rule)
  have two := independent.indepFun (i := false) (j := true) Bool.false_ne_true
  have rootIndependent := two.comp (measurable_fst.comp (measurable_pi_apply true))
    (measurable_pi_lambda _ (fun edge => measurable_pi_lambda _ (fun coordinate => measurable_pi_apply (edge, coordinate))))
  change IndepFun (fun sample => (sample ([], true)).1)
    (fun sample edge => electricalBoundaryTreeShift rule [edge] sample)
    (electricalBoundaryInnovationLaw rule p positive belowOne fixedPoint law) at rootIndependent
  have joint := rootIndependent.map_prod_eq_prod_map_map
    (measurable_fst.comp (measurable_pi_apply ([], true))).aemeasurable
    (measurable_pi_lambda _ (fun edge => electricalBoundaryTreeShift_measurable rule [edge])).aemeasurable
  dsimp only [Function.comp_def] at joint
  rw [joint, electricalBoundaryTreeChildren_map]
  congr 1
  change (Measure.infinitePi (fun coordinate : List (Fin rule.edges) × Bool =>
    (Rule.ConfigurationHistory.law rule p positive belowOne fixedPoint coordinate.2 0).prod (law : Measure ℝ≥0))).map
      (Prod.fst ∘ fun sample => sample ([], true)) = _
  rw [← Measure.map_map measurable_fst (measurable_pi_apply ([], true)), Measure.infinitePi_map_eval,
    Measure.map_fst_prod, measure_univ, one_smul]
  rfl

def electricalBoundaryTreeIteration (rule : Rule)
    (depth : ℕ) (sample : (List (Fin rule.edges) × Bool) → Configuration rule.edges × ℝ≥0) : ℝ≥0 :=
  match depth with
  | 0 => (sample ([], true)).2
  | depth+1 => electricalCellNNReal rule.network (sample ([], true)).1
      (fun edge => electricalBoundaryTreeIteration rule depth (electricalBoundaryTreeShift rule [edge] sample))

theorem electricalBoundaryTreeIteration_measurable (rule : Rule) (depth : ℕ) :
    Measurable (electricalBoundaryTreeIteration rule depth) := by
  induction depth with
  | zero => exact measurable_snd.comp (measurable_pi_apply ([], true))
  | succ depth previous =>
      exact (electricalCellNNReal_joint_continuous rule.network).measurable.comp
        ((measurable_fst.comp (measurable_pi_apply ([], true))).prodMk
          (measurable_pi_lambda _ (fun edge => previous.comp (electricalBoundaryTreeShift_measurable rule [edge]))))

theorem electricalBoundaryTreeIteration_law (rule : Rule) (p : ℝ) (positive : 0 < p)
    (belowOne : p < 1) (fixedPoint : rule.network.reliability p = p) (law : ProbabilityMeasure ℝ≥0) (depth : ℕ) :
    (electricalBoundaryInnovationLaw rule p positive belowOne fixedPoint law).map
      (electricalBoundaryTreeIteration rule depth) =
      ((electricalOutputLaw rule p positive belowOne fixedPoint)^[depth] law : Measure ℝ≥0) := by
  letI : ∀ coordinate : List (Fin rule.edges) × Bool,
      IsProbabilityMeasure (Rule.ConfigurationHistory.law rule p positive belowOne fixedPoint coordinate.2 0) :=
    fun coordinate => Rule.ConfigurationHistory.law_probability rule p positive belowOne fixedPoint coordinate.2 0
  induction depth with
  | zero =>
      change (Measure.infinitePi _).map (Prod.snd ∘ fun sample :
        (List (Fin rule.edges) × Bool) → Configuration rule.edges × ℝ≥0 => sample ([], true)) = _
      rw [← Measure.map_map measurable_snd (measurable_pi_apply ([], true)), Measure.infinitePi_map_eval,
        Measure.map_snd_prod, measure_univ, one_smul]
      rfl
  | succ depth previous =>
      have joint := electricalBoundaryTreeRoot_children_map rule p positive belowOne fixedPoint law
      rw [Measure.infinitePi_eq_pi] at joint
      have childMeasurable : Measurable (fun children : Fin rule.edges →
          ((List (Fin rule.edges) × Bool) → Configuration rule.edges × ℝ≥0) =>
          fun edge => electricalBoundaryTreeIteration rule depth (children edge)) :=
        measurable_pi_lambda _ (fun edge => (electricalBoundaryTreeIteration_measurable rule depth).comp (measurable_pi_apply edge))
      have transported := congrArg (fun measure => measure.map (Prod.map id
        (fun children : Fin rule.edges → ((List (Fin rule.edges) × Bool) → Configuration rule.edges × ℝ≥0) =>
          fun edge => electricalBoundaryTreeIteration rule depth (children edge)))) joint
      have jointMeasurable := (measurable_fst.comp (measurable_pi_apply ([], true))).prodMk
        (measurable_pi_lambda _ (fun edge => electricalBoundaryTreeShift_measurable rule [edge]))
      rw [Measure.map_map (f := fun sample : (List (Fin rule.edges) × Bool) → Configuration rule.edges × ℝ≥0 =>
          ((sample ([], true)).1, fun edge => electricalBoundaryTreeShift rule [edge] sample))
        (measurable_id.prodMap childMeasurable) jointMeasurable,
        ← Measure.map_prod_map _ _ measurable_id childMeasurable, Measure.map_id,
        Measure.pi_map_pi (fun _ => (electricalBoundaryTreeIteration_measurable rule depth).aemeasurable)] at transported
      simp_rw [previous] at transported
      change _ = (electricalInputLaw rule p positive belowOne fixedPoint
        ((electricalOutputLaw rule p positive belowOne fixedPoint)^[depth] law) :
          Measure (Configuration rule.edges × (Fin rule.edges → ℝ≥0))) at transported
      rw [Function.iterate_succ_apply']
      change _ = ((electricalInputLaw rule p positive belowOne fixedPoint
        ((electricalOutputLaw rule p positive belowOne fixedPoint)^[depth] law) :
          Measure (Configuration rule.edges × (Fin rule.edges → ℝ≥0))).map
            (fun data => electricalCellNNReal rule.network data.1 data.2))
      rw [← transported, Measure.map_map (electricalCellNNReal_joint_continuous rule.network).measurable
        (f := (Prod.map id (fun children : Fin rule.edges → ((List (Fin rule.edges) × Bool) → Configuration rule.edges × ℝ≥0) =>
          fun edge => electricalBoundaryTreeIteration rule depth (children edge))) ∘
          (fun sample : (List (Fin rule.edges) × Bool) → Configuration rule.edges × ℝ≥0 =>
            ((sample ([], true)).1, fun edge => electricalBoundaryTreeShift rule [edge] sample)))
        ((measurable_id.prodMap childMeasurable).comp jointMeasurable)]
      rfl

end
end IGSIII34.Percolation
