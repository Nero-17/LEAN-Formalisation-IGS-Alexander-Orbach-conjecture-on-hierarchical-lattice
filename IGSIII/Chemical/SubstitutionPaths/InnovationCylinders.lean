import IGSIII.Chemical.SubstitutionPaths.FiniteInnovationLaw

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

/-!
# Finite cylinders of the independent innovation probability space

Finite innovation trees are precisely finite collections of the independent
crossing/noncrossing marks. The explicit coordinate equivalence below keeps
both marks at every node, including the unused mark selected by neither mask.
-/

namespace IGSIII.Chemical.Substitution

open Universality Universality.FiniteNetwork MeasureTheory ProbabilityTheory
open scoped BigOperators

@[reducible] def FiniteInnovationNode (rule : Rule) : ℕ → Type
  | 0 => Unit
  | depth + 1 => Unit ⊕ (Fin rule.edges × FiniteInnovationNode rule depth)

instance finiteInnovationNodeFintype (rule : Rule) : (depth : ℕ) → Fintype (FiniteInnovationNode rule depth)
  | 0 => inferInstanceAs (Fintype Unit)
  | depth + 1 => by
      letI := finiteInnovationNodeFintype rule depth
      exact inferInstanceAs (Fintype (Unit ⊕ (Fin rule.edges × FiniteInnovationNode rule depth)))

noncomputable instance finiteInnovationNodeDecidableEq (rule : Rule) (depth : ℕ) :
    DecidableEq (FiniteInnovationNode rule depth) := Classical.decEq _

def finiteInnovationNodeAddress (rule : Rule) :
    (depth : ℕ) → FiniteInnovationNode rule depth → List (Fin rule.edges)
  | 0, _ => []
  | _ + 1, Sum.inl _ => []
  | depth + 1, Sum.inr (edge, node) => edge :: finiteInnovationNodeAddress rule depth node

theorem finiteInnovationNodeAddress_injective (rule : Rule) (depth : ℕ) :
    Function.Injective (finiteInnovationNodeAddress rule depth) := by
  induction depth with
  | zero => intro _ _ _; exact Subsingleton.elim _ _
  | succ depth inductionHypothesis =>
      intro first second equality
      cases first with
      | inl first =>
          cases second with
          | inl second => congr
          | inr second => simp [finiteInnovationNodeAddress] at equality
      | inr first =>
          cases second with
          | inl second => simp [finiteInnovationNodeAddress] at equality
          | inr second =>
              have equalParts := List.cons.inj equality
              exact congrArg Sum.inr (Prod.ext equalParts.1 (inductionHypothesis equalParts.2))

noncomputable def finiteInnovationCoordinatesEquiv (rule : Rule) : (depth : ℕ) →
    FiniteInnovationTree rule depth ≃
      ((FiniteInnovationNode rule depth × Bool) → Configuration rule.edges)
  | 0 =>
      { toFun := fun tree coordinate => tree coordinate.2
        invFun := fun coordinates opened => coordinates ((), opened)
        left_inv := fun _ => rfl
        right_inv := by intro coordinates; funext coordinate; rcases coordinate with ⟨⟨⟩, opened⟩; rfl }
  | depth + 1 =>
      { toFun := fun tree coordinate => match coordinate.1 with
          | Sum.inl _ => tree.1 coordinate.2
          | Sum.inr (edge, node) => finiteInnovationCoordinatesEquiv rule depth (tree.2 edge) (node, coordinate.2)
        invFun := fun coordinates =>
          (fun opened => coordinates (Sum.inl (), opened),
            fun edge => (finiteInnovationCoordinatesEquiv rule depth).symm
              (fun coordinate => coordinates (Sum.inr (edge, coordinate.1), coordinate.2)))
        left_inv := by
          intro tree
          apply Prod.ext
          · rfl
          · funext edge
            exact (finiteInnovationCoordinatesEquiv rule depth).symm_apply_apply (tree.2 edge)
        right_inv := by
          intro coordinates
          funext coordinate
          rcases coordinate with ⟨node, opened⟩
          cases node with
          | inl node => cases node; rfl
          | inr child =>
              exact congrFun ((finiteInnovationCoordinatesEquiv rule depth).apply_symm_apply
                (fun coordinate => coordinates (Sum.inr (child.1, coordinate.1), coordinate.2))) (child.2, opened) }

theorem finiteInnovationCoordinates_weight (rule : Rule) (p : ℝ) (depth : ℕ)
    (tree : FiniteInnovationTree rule depth) :
    finiteInnovationWeight rule p depth tree =
      ∏ coordinate : FiniteInnovationNode rule depth × Bool,
        rule.network.conditionalCellWeight p coordinate.2
          (finiteInnovationCoordinatesEquiv rule depth tree coordinate) := by
  induction depth with
  | zero =>
      rw [Fintype.prod_prod_type]
      simp only [finiteInnovationWeight, finiteInnovationCoordinatesEquiv, Equiv.coe_fn_mk,
        Fintype.prod_unique]
  | succ depth inductionHypothesis =>
      rw [Fintype.prod_prod_type, Fintype.prod_sum_type]
      simp only [finiteInnovationCoordinatesEquiv, Equiv.coe_fn_mk, Fintype.prod_unique]
      rw [Fintype.prod_prod_type]
      change _ = (∏ opened, rule.network.conditionalCellWeight p opened (tree.1 opened)) *
        ∏ edge, ∏ node, ∏ opened, rule.network.conditionalCellWeight p opened
          (finiteInnovationCoordinatesEquiv rule depth (tree.2 edge) (node, opened))
      simp only [finiteInnovationWeight]
      congr 1
      apply Finset.prod_congr rfl
      intro edge _
      rw [inductionHypothesis, Fintype.prod_prod_type]

noncomputable def finiteInnovationTreeFromMarks (rule : Rule)
    (marks : (List (Fin rule.edges) × Bool) → Configuration rule.edges) :
    (depth : ℕ) → List (Fin rule.edges) → FiniteInnovationTree rule depth
  | 0, address => fun opened => marks (address, opened)
  | depth + 1, address =>
      (fun opened => marks (address, opened),
        fun edge => finiteInnovationTreeFromMarks rule marks depth (address ++ [edge]))

theorem finiteInnovationTreeFromMarks_coordinates (rule : Rule)
    (marks : (List (Fin rule.edges) × Bool) → Configuration rule.edges)
    (depth : ℕ) (address : List (Fin rule.edges)) :
    finiteInnovationCoordinatesEquiv rule depth (finiteInnovationTreeFromMarks rule marks depth address) =
      fun coordinate => marks (address ++ finiteInnovationNodeAddress rule depth coordinate.1, coordinate.2) := by
  induction depth generalizing address with
  | zero => funext coordinate; simp [finiteInnovationCoordinatesEquiv, finiteInnovationTreeFromMarks,
      finiteInnovationNodeAddress]
  | succ depth inductionHypothesis =>
      funext coordinate
      rcases coordinate with ⟨node, opened⟩
      cases node with
      | inl node => simp [finiteInnovationCoordinatesEquiv, finiteInnovationTreeFromMarks,
          finiteInnovationNodeAddress]
      | inr child =>
          simpa only [finiteInnovationCoordinatesEquiv, finiteInnovationTreeFromMarks,
            Equiv.coe_fn_mk, finiteInnovationNodeAddress, List.append_assoc, List.singleton_append] using
              congrFun (inductionHypothesis (address ++ [child.1])) (child.2, opened)

theorem finiteInnovationTreeFromMarks_configuration (rule : Rule)
    (marks : (List (Fin rule.edges) × Bool) → Configuration rule.edges)
    (depth : ℕ) (address : List (Fin rule.edges)) (opened : Bool) :
    finiteInnovationConfiguration rule depth (finiteInnovationTreeFromMarks rule marks depth address) opened =
      markedGenerationConfiguration rule marks depth address opened := by
  induction depth generalizing address opened with
  | zero => rfl
  | succ depth inductionHypothesis =>
      change (generationTopCellsEquiv rule depth).symm _ = _
      simp only [finiteInnovationTreeFromMarks]
      simp_rw [inductionHypothesis]
      rfl

instance finiteInnovationTreeMeasurableSpace (rule : Rule) :
    (depth : ℕ) → MeasurableSpace (FiniteInnovationTree rule depth)
  | 0 => inferInstanceAs (MeasurableSpace (Bool → Configuration rule.edges))
  | depth + 1 => by
      letI := finiteInnovationTreeMeasurableSpace rule depth
      exact inferInstanceAs (MeasurableSpace ((Bool → Configuration rule.edges) ×
        (Fin rule.edges → FiniteInnovationTree rule depth)))

instance finiteInnovationTreeMeasurableSingletonClass (rule : Rule) :
    (depth : ℕ) → MeasurableSingletonClass (FiniteInnovationTree rule depth)
  | 0 => inferInstanceAs (MeasurableSingletonClass (Bool → Configuration rule.edges))
  | depth + 1 => by
      letI := finiteInnovationTreeMeasurableSpace rule depth
      letI := finiteInnovationTreeMeasurableSingletonClass rule depth
      exact inferInstanceAs (MeasurableSingletonClass ((Bool → Configuration rule.edges) ×
        (Fin rule.edges → FiniteInnovationTree rule depth)))

theorem finiteInnovationTreeFromMarks_measurable (rule : Rule)
    (depth : ℕ) (address : List (Fin rule.edges)) :
    Measurable (fun marks => finiteInnovationTreeFromMarks rule marks depth address) := by
  have representation : (fun marks => finiteInnovationTreeFromMarks rule marks depth address) =
      fun marks => (finiteInnovationCoordinatesEquiv rule depth).symm
        (fun coordinate => marks
          (address ++ finiteInnovationNodeAddress rule depth coordinate.1, coordinate.2)) := by
    funext marks
    rw [← finiteInnovationTreeFromMarks_coordinates, Equiv.symm_apply_apply]
  rw [representation]
  exact (measurable_of_countable _).comp (by fun_prop)

theorem markedGenerationConfiguration_measurable (rule : Rule)
    (depth : ℕ) (address : List (Fin rule.edges)) (opened : Bool) :
    Measurable (fun marks => markedGenerationConfiguration rule marks depth address opened) := by
  have measurable := (measurable_of_countable
    (fun tree : FiniteInnovationTree rule depth => finiteInnovationConfiguration rule depth tree opened)).comp
      (finiteInnovationTreeFromMarks_measurable rule depth address)
  simpa only [Function.comp_def, finiteInnovationTreeFromMarks_configuration] using measurable

noncomputable def finiteInnovationTreeLaw (rule : Rule) (p : ℝ) (positive : 0 < p)
    (lessOne : p < 1) (fixedPoint : rule.network.reliability p = p) (depth : ℕ) :
    Measure (FiniteInnovationTree rule depth) :=
  (finiteWeightPMF (finiteInnovationWeight rule p depth)
    (finiteInnovationWeight_nonneg rule p positive.le lessOne.le depth)
    (finiteInnovationWeight_sum rule p positive lessOne fixedPoint depth)).toMeasure

theorem finiteInnovationCoordinates_map (rule : Rule) (p : ℝ) (positive : 0 < p)
    (lessOne : p < 1) (fixedPoint : rule.network.reliability p = p) (depth : ℕ) :
    (Measure.pi (fun coordinate : FiniteInnovationNode rule depth × Bool =>
      Rule.ConfigurationHistory.law rule p positive lessOne fixedPoint coordinate.2 0)).map
        (finiteInnovationCoordinatesEquiv rule depth).symm =
      finiteInnovationTreeLaw rule p positive lessOne fixedPoint depth := by
  letI : ∀ coordinate : FiniteInnovationNode rule depth × Bool,
      IsProbabilityMeasure (Rule.ConfigurationHistory.law rule p positive lessOne fixedPoint coordinate.2 0) :=
    fun coordinate => Rule.ConfigurationHistory.law_probability rule p positive lessOne fixedPoint coordinate.2 0
  apply Measure.ext_of_singleton
  intro tree
  rw [Measure.map_apply (measurable_of_countable _) (measurableSet_singleton tree)]
  have preimage : (finiteInnovationCoordinatesEquiv rule depth).symm ⁻¹' {tree} =
      {finiteInnovationCoordinatesEquiv rule depth tree} := by
    ext coordinates
    simp only [Set.mem_preimage, Set.mem_singleton_iff, Equiv.symm_apply_eq]
  rw [preimage, Measure.pi_singleton]
  change _ = (finiteWeightPMF _ _ _).toMeasure {tree}
  rw [finiteWeightPMF_singleton]
  simp only [Rule.ConfigurationHistory.law, finiteWeightPMF_singleton,
    Rule.ConfigurationHistory.recursiveWeight]
  rw [← ENNReal.ofReal_prod_of_nonneg (fun coordinate _ =>
    rule.network.conditionalCellWeight_nonneg positive.le lessOne.le coordinate.2 _),
    ← finiteInnovationCoordinates_weight]

theorem finiteInnovationNodeCoordinate_injective (rule : Rule) (depth : ℕ)
    (address : List (Fin rule.edges)) :
    Function.Injective (fun coordinate : FiniteInnovationNode rule depth × Bool =>
      (address ++ finiteInnovationNodeAddress rule depth coordinate.1, coordinate.2)) := by
  intro first second equality
  have equalAddresses : finiteInnovationNodeAddress rule depth first.1 =
      finiteInnovationNodeAddress rule depth second.1 := by
    simpa only [List.append_cancel_left_eq] using congrArg Prod.fst equality
  have equalStates : first.2 = second.2 :=
    congrArg (fun coordinate : List (Fin rule.edges) × Bool => coordinate.2) equality
  exact Prod.ext (finiteInnovationNodeAddress_injective rule depth equalAddresses)
    equalStates

/-- The finite tree is the actual finite restriction of the countable
independent-mark probability space, with its exact product weight. -/
theorem independentInnovationLaw_finite_tree (rule : Rule) (p : ℝ) (positive : 0 < p)
    (lessOne : p < 1) (fixedPoint : rule.network.reliability p = p)
    (depth : ℕ) (address : List (Fin rule.edges)) :
    (independentInnovationLaw rule p positive lessOne fixedPoint).map
        (fun marks => finiteInnovationTreeFromMarks rule marks depth address) =
      finiteInnovationTreeLaw rule p positive lessOne fixedPoint depth := by
  letI : ∀ coordinate : List (Fin rule.edges) × Bool,
      IsProbabilityMeasure (Rule.ConfigurationHistory.law rule p positive lessOne fixedPoint coordinate.2 0) :=
    fun coordinate => Rule.ConfigurationHistory.law_probability rule p positive lessOne fixedPoint coordinate.2 0
  letI : ∀ coordinate : FiniteInnovationNode rule depth × Bool,
      IsProbabilityMeasure (Rule.ConfigurationHistory.law rule p positive lessOne fixedPoint coordinate.2 0) :=
    fun coordinate => Rule.ConfigurationHistory.law_probability rule p positive lessOne fixedPoint coordinate.2 0
  have restricted := Measure.map_infinitePi_infinitePi_of_inj
    (P := fun coordinate : List (Fin rule.edges) × Bool =>
      Rule.ConfigurationHistory.law rule p positive lessOne fixedPoint coordinate.2 0)
    (finiteInnovationNodeCoordinate_injective rule depth address)
  rw [Measure.infinitePi_eq_pi (μ := fun coordinate : FiniteInnovationNode rule depth × Bool =>
    Rule.ConfigurationHistory.law rule p positive lessOne fixedPoint coordinate.2 0)] at restricted
  change (independentInnovationLaw rule p positive lessOne fixedPoint).map
    (fun marks (coordinate : FiniteInnovationNode rule depth × Bool) => marks
      (address ++ finiteInnovationNodeAddress rule depth coordinate.1, coordinate.2)) = _ at restricted
  calc
    (independentInnovationLaw rule p positive lessOne fixedPoint).map
        (fun marks => finiteInnovationTreeFromMarks rule marks depth address) =
      ((independentInnovationLaw rule p positive lessOne fixedPoint).map
        (fun marks coordinate => marks
          (address ++ finiteInnovationNodeAddress rule depth coordinate.1, coordinate.2))).map
          (finiteInnovationCoordinatesEquiv rule depth).symm := by
            rw [Measure.map_map (measurable_of_countable _) (by fun_prop)]
            congr 1
            funext marks
            rw [Function.comp_apply, ← finiteInnovationTreeFromMarks_coordinates,
              Equiv.symm_apply_apply]
    _ = (Measure.pi (fun coordinate : FiniteInnovationNode rule depth × Bool =>
        Rule.ConfigurationHistory.law rule p positive lessOne fixedPoint coordinate.2 0)).map
          (finiteInnovationCoordinatesEquiv rule depth).symm := by rw [restricted]
    _ = finiteInnovationTreeLaw rule p positive lessOne fixedPoint depth :=
      finiteInnovationCoordinates_map rule p positive lessOne fixedPoint depth

theorem finite_weight_observable_map
    {source target : Type*} [Fintype source] [Fintype target]
    [MeasurableSpace source] [MeasurableSingletonClass source]
    [MeasurableSpace target] [MeasurableSingletonClass target]
    (sourceWeight : source → ℝ) (sourceNonnegative : ∀ sample, 0 ≤ sourceWeight sample)
    (sourceMass : ∑ sample, sourceWeight sample = 1)
    (targetWeight : target → ℝ) (targetNonnegative : ∀ output, 0 ≤ targetWeight output)
    (targetMass : ∑ output, targetWeight output = 1) (transport : source → target)
    (observableLaw : ∀ response : target → ℝ,
      (∑ sample, sourceWeight sample * response (transport sample)) =
        ∑ output, targetWeight output * response output) :
    (finiteWeightPMF sourceWeight sourceNonnegative sourceMass).toMeasure.map transport =
      (finiteWeightPMF targetWeight targetNonnegative targetMass).toMeasure := by
  classical
  rw [PMF.toMeasure_map transport _ (measurable_of_countable transport)]
  congr 1
  ext output
  simp only [PMF.map_apply, tsum_fintype, finiteWeightPMF_apply]
  have atom : (∑ sample, if output = transport sample then sourceWeight sample else 0) =
      targetWeight output := by
    simpa [mul_ite] using observableLaw (fun selected => if output = selected then 1 else 0)
  have castAtom := congrArg ENNReal.ofReal atom
  rw [ENNReal.ofReal_sum_of_nonneg (fun sample _ => by
    split_ifs
    · exact sourceNonnegative sample
    · exact le_rfl)] at castAtom
  simpa only [apply_ite, ENNReal.ofReal_zero] using castAtom

theorem finiteInnovationTreeLaw_history (rule : Rule) (p : ℝ) (positive : 0 < p)
    (lessOne : p < 1) (fixedPoint : rule.network.reliability p = p)
    (depth : ℕ) (opened : Bool) :
    (finiteInnovationTreeLaw rule p positive lessOne fixedPoint depth).map
        (fun tree => Rule.ConfigurationHistory.ofFine rule depth
          (finiteInnovationConfiguration rule depth tree opened)) =
      Rule.ConfigurationHistory.law rule p positive lessOne fixedPoint opened depth := by
  apply finite_weight_observable_map
  exact finite_innovation_history_observable rule p positive lessOne fixedPoint opened depth

/-- All finite histories produced from the common independent mark space
have exactly the original IGS II history law. Thus every finite cylinder of
the multilevel configurations is identified, including all noncrossing cells. -/
theorem independentInnovationLaw_history_marginal (rule : Rule) (p : ℝ) (positive : 0 < p)
    (lessOne : p < 1) (fixedPoint : rule.network.reliability p = p)
    (depth : ℕ) (address : List (Fin rule.edges)) (opened : Bool) :
    (independentInnovationLaw rule p positive lessOne fixedPoint).map
        (fun marks => Rule.ConfigurationHistory.ofFine rule depth
          (markedGenerationConfiguration rule marks depth address opened)) =
      Rule.ConfigurationHistory.law rule p positive lessOne fixedPoint opened depth := by
  calc
    (independentInnovationLaw rule p positive lessOne fixedPoint).map
        (fun marks => Rule.ConfigurationHistory.ofFine rule depth
          (markedGenerationConfiguration rule marks depth address opened)) =
      ((independentInnovationLaw rule p positive lessOne fixedPoint).map
        (fun marks => finiteInnovationTreeFromMarks rule marks depth address)).map
          (fun tree => Rule.ConfigurationHistory.ofFine rule depth
            (finiteInnovationConfiguration rule depth tree opened)) := by
              rw [Measure.map_map (measurable_of_countable _) ]
              · congr 1
                funext marks
                rw [Function.comp_apply, finiteInnovationTreeFromMarks_configuration]
              · exact finiteInnovationTreeFromMarks_measurable rule depth address
    _ = Rule.ConfigurationHistory.law rule p positive lessOne fixedPoint opened depth := by
      rw [independentInnovationLaw_finite_tree, finiteInnovationTreeLaw_history]

end IGSIII.Chemical.Substitution
