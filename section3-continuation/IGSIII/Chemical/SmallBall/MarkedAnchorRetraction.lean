import IGSIII.Chemical.SmallBall.MarkedSkeletonDistortion

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

namespace IGSIII.Chemical.SmallBall

open Universality Universality.FiniteNetwork MeasureTheory Substitution IGSIII.Geometry Filter Set
open scoped ENNReal Topology

noncomputable section

theorem anchorRetraction_measurable {Index Source : Type*} [Finite Index]
    [MeasurableSpace Index] [MeasurableSpace Source] [MeasurableSingletonClass Source]
    (embedding : Index ↪ Source) (projection : Source → Index) (projectionMeasurable : Measurable projection) :
    Measurable (anchorRetraction embedding projection) := by
  classical
  intro event eventMeasurable
  have equality : (anchorRetraction embedding projection) ⁻¹' event =
      (embedding '' event) ∪ (Set.range embedding)ᶜ ∩ (projection ⁻¹' event) := by
    ext point
    by_cases membership : ∃ anchor, embedding anchor = point
    · obtain ⟨anchor, rfl⟩ := membership
      rw [Set.mem_preimage, anchorRetraction_embedding]
      constructor
      · intro inside
        exact Or.inl ⟨anchor, inside, rfl⟩
      · rintro (⟨other, inside, equality⟩ | ⟨outside, _⟩)
        · exact (embedding.injective equality) ▸ inside
        · exact False.elim (outside ⟨anchor, rfl⟩)
    · simp only [Set.mem_preimage, anchorRetraction, dif_neg membership]
      constructor
      · intro inside
        exact Or.inr ⟨membership, inside⟩
      · rintro (⟨anchor, _, equality⟩ | ⟨_, inside⟩)
        · exact False.elim (membership ⟨anchor, equality⟩)
        · exact inside
  rw [equality]
  exact ((Set.toFinite event).image embedding).measurableSet.union
    ((Set.finite_range embedding).measurableSet.compl.inter (projectionMeasurable eventMeasurable))

variable (rule : Rule) (classicalRule : rule.Classical)
variable (configuration : ∀ depth, Configuration (rule.generation depth).edges)
variable (coherent : configurationSequenceCoherent rule configuration)
variable (crossing : ∀ depth, (rule.generation depth).network.crosses (configuration depth) = true)
variable (scale : ℝ) (scalePositive : 0 < scale)
variable (limitLength : ∀ coarse, Fin (rule.generation coarse).edges → ℝ)
variable (lengthNonnegative : ∀ depth edge, 0 ≤ limitLength depth edge)
variable (lengthPositive : ∀ depth edge, configuration depth edge = true → 0 < limitLength depth edge)
variable (childConvergence : ∀ coarse edge, Tendsto (fun fine =>
  (((rule.generation fine).network.openGraph
    (generationBlockCells rule coarse fine (configuration (coarse + fine + 1)) edge)).dist
      (rule.generation fine).network.source (rule.generation fine).network.target : ℝ) /
    scale ^ (coarse + fine + 2)) atTop (𝓝 (limitLength coarse edge)))

def actualChemicalVertexEmbedding (age : ℕ) :
    RetainedSkeletonVertex (rule.generation age).network (configuration age) ↪
      ActualChemicalSpace rule classicalRule configuration coherent scale scalePositive limitLength lengthNonnegative lengthPositive childConvergence where
  toFun := actualChemicalVertex rule classicalRule configuration coherent scale scalePositive limitLength lengthNonnegative lengthPositive childConvergence age
  inj' := by
    intro first last equality
    letI := actualSkeletonMetric (rule.generation age).network (classicalRule.generation age).simple
      (configuration age) (limitLength age) (lengthNonnegative age) (lengthPositive age)
    apply dist_eq_zero.mp
    change weightedDistance ((rule.generation age).network.openGraph (configuration age))
      (indexedBondCost (rule.generation age).network (limitLength age)) first.val last.val = 0
    rw [← actualChemicalVertex_distance rule classicalRule configuration coherent scale scalePositive limitLength lengthNonnegative lengthPositive
      childConvergence age first last, equality, dist_self]

theorem actualChemicalSpace_terminal_projection_identity (age : ℕ)
    (projection : ActualChemicalSpace rule classicalRule configuration coherent scale scalePositive limitLength lengthNonnegative lengthPositive
      childConvergence → RetainedSkeletonVertex (rule.generation age).network (configuration age)) (sourceSide : Bool) :
    actualChemicalVertex rule classicalRule configuration coherent scale scalePositive limitLength lengthNonnegative lengthPositive childConvergence age
      (anchorRetraction (actualChemicalVertexEmbedding rule classicalRule configuration coherent scale scalePositive limitLength lengthNonnegative
        lengthPositive childConvergence age) projection
        (actualChemicalTerminal rule classicalRule configuration coherent crossing scale scalePositive limitLength lengthNonnegative lengthPositive
          childConvergence sourceSide)) =
      actualChemicalTerminal rule classicalRule configuration coherent crossing scale scalePositive limitLength lengthNonnegative lengthPositive
        childConvergence sourceSide := by
  rw [actualChemicalTerminal_eq_vertex rule classicalRule configuration coherent crossing scale scalePositive limitLength lengthNonnegative
    lengthPositive childConvergence age sourceSide]
  change actualChemicalVertex rule classicalRule configuration coherent scale scalePositive limitLength lengthNonnegative lengthPositive childConvergence age
    (anchorRetraction (actualChemicalVertexEmbedding rule classicalRule configuration coherent scale scalePositive limitLength lengthNonnegative
      lengthPositive childConvergence age) projection
      ((actualChemicalVertexEmbedding rule classicalRule configuration coherent scale scalePositive limitLength lengthNonnegative
        lengthPositive childConvergence age) (retainedTerminalVertex rule configuration crossing age sourceSide))) = _
  rw [anchorRetraction_embedding]

end
end IGSIII.Chemical.SmallBall