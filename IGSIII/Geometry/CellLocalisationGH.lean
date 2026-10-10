import IGSIII.Geometry.RootedComponentGromovHausdorff
import IGSIII.Probability.IndependentPrefix
import Mathlib.MeasureTheory.Constructions.BorelSpace.Metrizable
import Mathlib.Probability.Independence.InfinitePi

set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option backward.isDefEq.respectTransparency false
namespace IGSIII.Geometry
noncomputable section
open Universality Universality.FiniteNetwork IGSIII.Chemical.Substitution IGSIII.Probability
open MeasureTheory ProbabilityTheory GromovHausdorff Filter
open scoped Topology ENNReal

instance chemicalGHSpaceMeasurableSpace : MeasurableSpace GHSpace := borel GHSpace
instance chemicalGHSpaceBorelSpace : BorelSpace GHSpace := ⟨rfl⟩

theorem rootedFiniteComponentGH_configuration_congr (rule : Rule)
    (configuration otherConfiguration : ∀ depth, Configuration (rule.generation depth).edges)
    (sourceSide : Bool) (scale : ℝ) (scalePositive : 0 < scale) (offset depth : ℕ)
    (same : configuration depth = otherConfiguration depth) :
    toGHSpace (RootedFiniteComponent rule configuration sourceSide scale scalePositive offset depth) =
      toGHSpace (RootedFiniteComponent rule otherConfiguration sourceSide scale scalePositive offset depth) := by
  apply toGHSpace_eq_toGHSpace_iff_isometryEquiv.mpr
  let equivalence : RootedFiniteComponent rule configuration sourceSide scale scalePositive offset depth ≃
      RootedFiniteComponent rule otherConfiguration sourceSide scale scalePositive offset depth :=
    Equiv.subtypeEquivRight (fun _ => by rw [same])
  refine ⟨{ toEquiv := equivalence, isometry_toFun := ?_ }⟩
  apply Isometry.of_dist_eq
  intro first last
  change (((rule.generation depth).network.openGraph (otherConfiguration depth)).dist first.val last.val : ℝ) / scale ^ (depth + 1 + offset) =
    (((rule.generation depth).network.openGraph (configuration depth)).dist first.val last.val : ℝ) / scale ^ (depth + 1 + offset)
  exact congrArg (fun state : Configuration (rule.generation depth).edges =>
    (((rule.generation depth).network.openGraph state).dist first.val last.val : ℝ) / scale ^ (depth + 1 + offset)) same.symm

def configurationAtDepth (rule : Rule) (depth : ℕ) (configuration : Configuration (rule.generation depth).edges) :
    ∀ age, Configuration (rule.generation age).edges := by
  classical
  exact Function.update (fun _ _ => false) depth configuration

@[simp] theorem configurationAtDepth_self (rule : Rule) (depth : ℕ) (configuration : Configuration (rule.generation depth).edges) :
    configurationAtDepth rule depth configuration depth = configuration := by
  classical
  exact Function.update_self _ _ _

/-- Actual microscopic planted components as points of the Polish space of
compact metric spaces. All four choices retain their common C/N innovations. -/
def markedRootedFiniteGH (rule : Rule) (scale : ℝ) (scalePositive : 0 < scale) (depth : ℕ)
    (marks : (List (Fin rule.edges) × Bool) → Configuration rule.edges) (opened sourceSide : Bool) : GHSpace :=
  toGHSpace (RootedFiniteComponent rule (fun age => markedGenerationConfiguration rule marks age [] opened)
    sourceSide scale scalePositive 0 depth)

theorem markedRootedFiniteGH_measurable (rule : Rule) (scale : ℝ) (scalePositive : 0 < scale) (depth : ℕ) :
    Measurable (markedRootedFiniteGH rule scale scalePositive depth) := by
  apply measurable_pi_lambda
  intro opened
  apply measurable_pi_lambda
  intro sourceSide
  let response : Configuration (rule.generation depth).edges → GHSpace := fun configuration =>
    toGHSpace (RootedFiniteComponent rule (configurationAtDepth rule depth configuration) sourceSide scale scalePositive 0 depth)
  have factorization : (fun marks => markedRootedFiniteGH rule scale scalePositive depth marks opened sourceSide) =
      response ∘ (fun marks => markedGenerationConfiguration rule marks depth [] opened) := by
    funext marks
    exact rootedFiniteComponentGH_configuration_congr rule _ _ sourceSide scale scalePositive 0 depth
      (configurationAtDepth_self rule depth _).symm
  rw [factorization]
  exact (measurable_of_finite response).comp (markedGenerationConfiguration_measurable rule depth [] opened)

end
end IGSIII.Geometry

