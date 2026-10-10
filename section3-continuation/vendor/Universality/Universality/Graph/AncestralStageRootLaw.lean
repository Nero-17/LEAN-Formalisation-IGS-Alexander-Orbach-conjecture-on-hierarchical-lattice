import Universality.Graph.AncestralProbabilitySpace
import Universality.Graph.AncestralPrefix
import Universality.Graph.FiniteUniformLaw

namespace Universality.Rule
noncomputable section
attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false
open MeasureTheory ProbabilityTheory

abbrev AncestralAgeFiber (rule : Rule) (age n : ℕ) :=
  {vertex : (rule.generation (age + n)).network.InteriorVertex //
    rule.interiorVertexAge (age + n) vertex = age}

instance ancestralAgeFiber_nonempty (rule : Rule)
    [Nonempty rule.network.InteriorVertex] [NeZero rule.edges] (age n : ℕ) :
    Nonempty (rule.AncestralAgeFiber age n) :=
  (rule.ancestralPrefixEquiv age n).symm.nonempty

/-- The uniform law on the actual age fibre, viewed as vertices of the actual
finite generation. -/
def ancestralAgeFiberRootLaw (rule : Rule)
    [Nonempty rule.network.InteriorVertex] [NeZero rule.edges] (age n : ℕ) :
    Measure (Fin (rule.generation (age + n)).vertices) :=
  (PMF.uniformOfFintype (rule.AncestralAgeFiber age n)).toMeasure.map
    (fun vertex => vertex.val.val)

instance ancestralAgeFiberRootLaw_probability (rule : Rule)
    [Nonempty rule.network.InteriorVertex] [NeZero rule.edges] (age n : ℕ) :
    IsProbabilityMeasure (rule.ancestralAgeFiberRootLaw age n) := by
  unfold ancestralAgeFiberRootLaw
  exact Measure.isProbabilityMeasure_map (measurable_of_countable _).aemeasurable

def ancestralRootAtStage (rule : Rule) (age n : ℕ)
    (input : Fin (rule.generation age).vertices × (ℕ → Fin rule.edges)) :
    Fin (rule.generation (age + n)).vertices :=
  (rule.ancestralTower age input.2).vertexMap 0 n (Nat.zero_le n) input.1

theorem measurable_ancestralRootAtStage (rule : Rule) (age n : ℕ) :
    Measurable (rule.ancestralRootAtStage age n) := by
  letI : MeasurableSpace Bool := ⊤
  letI : MeasurableSingletonClass Bool := ⟨fun _ => trivial⟩
  have hinput : Measurable (fun input : Fin (rule.generation age).vertices ×
      (ℕ → Fin rule.edges) => (input.1, (input.2, fun _ => false)) :
      _ → rule.AncestralSample age) :=
    measurable_fst.prodMk (measurable_snd.prodMk measurable_const)
  intro target htarget
  exact hinput ((rule.measurable_ancestralSampleStageRoot age n) htarget)

theorem ancestralSeedStageRoot_measurePreserving (rule : Rule)
    [Nonempty rule.network.InteriorVertex] [NeZero rule.edges] (age n : ℕ) :
    MeasurePreserving (fun input : rule.network.InteriorVertex × (ℕ → Fin rule.edges) =>
      rule.ancestralRootAtStage age n ((rule.ancestralRootInterior age input.1).val, input.2))
      ((PMF.uniformOfFintype rule.network.InteriorVertex).toMeasure.prod rule.ancestralSpineLaw)
      (rule.ancestralAgeFiberRootLaw age n) := by
  have hprefix := (MeasurePreserving.id
    (PMF.uniformOfFintype rule.network.InteriorVertex).toMeasure).prod
      (Universality.finiteUniform_prefix_measurePreserving (α := Fin rule.edges) n)
  rw [Universality.finiteUniform_prod] at hprefix
  have hequiv := (Universality.finiteUniform_equiv_measurePreserving
    (rule.ancestralPrefixEquiv age n)).comp hprefix
  have hvertex := ((measurable_of_countable
    (fun vertex : rule.AncestralAgeFiber age n => vertex.val.val)).measurePreserving
      (PMF.uniformOfFintype (rule.AncestralAgeFiber age n)).toMeasure).comp hequiv
  have heq : (fun input : rule.network.InteriorVertex × (ℕ → Fin rule.edges) =>
      (rule.ancestralPrefixEquiv age n (input.1, fun i => input.2 i.val)).val.val) =
      (fun input => rule.ancestralRootAtStage age n
        ((rule.ancestralRootInterior age input.1).val, input.2)) := by
    funext input
    exact rule.ancestralPrefixEquiv_towerRoot age n input.1 input.2
  change MeasurePreserving (fun input : rule.network.InteriorVertex × (ℕ → Fin rule.edges) =>
    (rule.ancestralPrefixEquiv age n (input.1, fun i => input.2 i.val)).val.val) _ _ at hvertex
  rw [heq] at hvertex
  exact hvertex

/-- The physical tower root has exactly the uniform actual age-fibre law.
The root distribution is derived from the finite-prefix bijection. -/
theorem ancestralRootAtStage_measurePreserving (rule : Rule)
    [Nonempty rule.network.InteriorVertex] [NeZero rule.edges] (age n : ℕ) :
    MeasurePreserving (rule.ancestralRootAtStage age n)
      ((rule.ancestralInitialRootLaw age).prod rule.ancestralSpineLaw)
      (rule.ancestralAgeFiberRootLaw age n) := by
  have hinitial := ((measurable_of_countable
    (fun seed : rule.network.InteriorVertex => (rule.ancestralRootInterior age seed).val)).measurePreserving
      (PMF.uniformOfFintype rule.network.InteriorVertex).toMeasure).prod
        (MeasurePreserving.id rule.ancestralSpineLaw)
  have hseed := rule.ancestralSeedStageRoot_measurePreserving age n
  have hresult := hseed.map_of_comp
    (f := Prod.map (fun seed : rule.network.InteriorVertex =>
      (rule.ancestralRootInterior age seed).val) id)
    (g := rule.ancestralRootAtStage age n)
    (rule.measurable_ancestralRootAtStage age n) hinitial.measurable
  rw [hinitial.map_eq] at hresult
  exact hresult

end
end Universality.Rule
