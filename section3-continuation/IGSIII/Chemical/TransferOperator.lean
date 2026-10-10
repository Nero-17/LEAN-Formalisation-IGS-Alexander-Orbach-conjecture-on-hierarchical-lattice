import IGSIII.Chemical.ShortestLp
import IGSIII.Chemical.SubstitutionPaths.IndexedPaths
import IGSIII.Probability.IndependentTreeChildren

/-! The actual min-plus transfer on the common innovation space and on Lp. -/

set_option autoImplicit false

namespace IGSIII.Chemical.Substitution

open Universality Universality.FiniteNetwork MeasureTheory ProbabilityTheory
open IGSIII.Probability
open scoped ENNReal

noncomputable def chemicalTransfer (rule : Rule)
    (value : ((List (Fin rule.edges) × Bool) → Configuration rule.edges) → ℝ)
    (marks : (List (Fin rule.edges) × Bool) → Configuration rule.edges) : ℝ :=
  (edgePathFamily rule.network (marks ([], true))).shortest
    (fun edge => value (innovationTreeShift rule [edge] marks))

theorem chemicalTransfer_memLp (rule : Rule) (p : ℝ) (positive : 0 < p)
    (belowOne : p < 1) (fixedPoint : rule.network.reliability p = p)
    {value : ((List (Fin rule.edges) × Bool) → Configuration rule.edges) → ℝ}
    {order : ℝ≥0∞}
    (integrable : MemLp value order (independentInnovationLaw rule p positive belowOne fixedPoint)) :
    MemLp (chemicalTransfer rule value) order (independentInnovationLaw rule p positive belowOne fixedPoint) :=
  PathFamily.shortest_random_memLp (fun configuration => edgePathFamily rule.network configuration)
    (measurable_pi_apply ([], true)).aemeasurable
    (fun edge => innovationTreeShift_memLp rule p positive belowOne fixedPoint [edge] integrable)

noncomputable def chemicalTransferLp (rule : Rule) (p : ℝ) (positive : 0 < p)
    (belowOne : p < 1) (fixedPoint : rule.network.reliability p = p) (order : ℝ≥0∞)
    (value : Lp ℝ order (independentInnovationLaw rule p positive belowOne fixedPoint)) :
    Lp ℝ order (independentInnovationLaw rule p positive belowOne fixedPoint) :=
  (chemicalTransfer_memLp rule p positive belowOne fixedPoint (Lp.memLp value)).toLp
    (chemicalTransfer rule value)

theorem chemicalTransferLp_coe_ae (rule : Rule) (p : ℝ) (positive : 0 < p)
    (belowOne : p < 1) (fixedPoint : rule.network.reliability p = p) (order : ℝ≥0∞)
    (value : Lp ℝ order (independentInnovationLaw rule p positive belowOne fixedPoint)) :
    ⇑(chemicalTransferLp rule p positive belowOne fixedPoint order value) =ᵐ[
      independentInnovationLaw rule p positive belowOne fixedPoint] chemicalTransfer rule value :=
  MemLp.coeFn_toLp _

theorem chemicalTransfer_mono (rule : Rule)
    {first second : ((List (Fin rule.edges) × Bool) → Configuration rule.edges) → ℝ}
    (comparison : first ≤ second) : chemicalTransfer rule first ≤ chemicalTransfer rule second := by
  intro marks
  exact (edgePathFamily rule.network (marks ([], true))).shortest_mono
    (fun edge => comparison (innovationTreeShift rule [edge] marks))

theorem chemicalTransfer_scale (rule : Rule)
    (value : ((List (Fin rule.edges) × Bool) → Configuration rule.edges) → ℝ)
    {scalar : ℝ} (nonnegative : 0 ≤ scalar) :
    chemicalTransfer rule (fun marks => scalar * value marks) =
      fun marks => scalar * chemicalTransfer rule value marks := by
  funext marks
  exact (edgePathFamily rule.network (marks ([], true))).shortest_scale _ nonnegative

theorem chemicalTransfer_superadditive (rule : Rule)
    (first second : ((List (Fin rule.edges) × Bool) → Configuration rule.edges) → ℝ) :
    (fun marks => chemicalTransfer rule first marks + chemicalTransfer rule second marks) ≤
      chemicalTransfer rule (first + second) := by
  intro marks
  exact (edgePathFamily rule.network (marks ([], true))).shortest_superadditive _ _

theorem chemicalTransfer_congr_ae (rule : Rule) (p : ℝ) (positive : 0 < p)
    (belowOne : p < 1) (fixedPoint : rule.network.reliability p = p)
    {first second : ((List (Fin rule.edges) × Bool) → Configuration rule.edges) → ℝ}
    (equal : first =ᵐ[independentInnovationLaw rule p positive belowOne fixedPoint] second) :
    chemicalTransfer rule first =ᵐ[independentInnovationLaw rule p positive belowOne fixedPoint]
      chemicalTransfer rule second := by
  have coordinates : ∀ edge : Fin rule.edges,
      (fun marks => first (innovationTreeShift rule [edge] marks)) =ᵐ[
        independentInnovationLaw rule p positive belowOne fixedPoint]
      (fun marks => second (innovationTreeShift rule [edge] marks)) :=
    fun edge => (innovationTreeShift_preserving rule p positive belowOne fixedPoint [edge]).quasiMeasurePreserving.ae_eq_comp equal
  filter_upwards [ae_all_iff.mpr coordinates] with marks equality
  unfold chemicalTransfer
  congr 1
  exact funext equality

theorem chemicalTransfer_mono_ae (rule : Rule) (p : ℝ) (positive : 0 < p)
    (belowOne : p < 1) (fixedPoint : rule.network.reliability p = p)
    {first second : ((List (Fin rule.edges) × Bool) → Configuration rule.edges) → ℝ}
    (comparison : first ≤ᵐ[independentInnovationLaw rule p positive belowOne fixedPoint] second) :
    chemicalTransfer rule first ≤ᵐ[independentInnovationLaw rule p positive belowOne fixedPoint]
      chemicalTransfer rule second := by
  have coordinates : ∀ edge : Fin rule.edges,
      ∀ᵐ marks ∂independentInnovationLaw rule p positive belowOne fixedPoint,
        first (innovationTreeShift rule [edge] marks) ≤ second (innovationTreeShift rule [edge] marks) :=
    fun edge => (innovationTreeShift_preserving rule p positive belowOne fixedPoint [edge]).quasiMeasurePreserving.ae comparison
  filter_upwards [ae_all_iff.mpr coordinates] with marks inequalities
  exact (edgePathFamily rule.network (marks ([], true))).shortest_mono inequalities

end IGSIII.Chemical.Substitution
