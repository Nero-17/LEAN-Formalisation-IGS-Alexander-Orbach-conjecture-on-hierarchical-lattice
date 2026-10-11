import IGSIII34.ResistanceLimit.ActualBlockZeroPersistence
import IGSIII34.Forms.CoherentSkeletonPotential

set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option backward.isDefEq.respectTransparency false
namespace IGSIII34.ResistanceLimit
noncomputable section
open Universality Universality.FiniteNetwork IGSIII.Geometry IGSIII34.Forms

theorem finitePotential_apply_index_cast (sizes : ℕ → ℕ)
    (potentials : ∀ index, Fin (sizes index) → ℝ)
    {first last : ℕ} (equal : first = last) (cast : sizes last = sizes first) (vertex : Fin (sizes last)) :
    potentials first (Fin.cast cast vertex) = potentials last vertex := by
  subst last
  rfl

def actualBlockZeroTowerStage (rule : Rule) (coarse : ℕ)
    (chosen : Fin (rule.generation coarse).edges)
    (potentials : ∀ fine, Fin (rule.generation fine).vertices → ℝ)
    (depth : ℕ) (vertex : Fin (rule.generation depth).vertices) : ℝ :=
  if large : coarse + 1 ≤ depth then
    actualBlockZeroExtension rule coarse (depth - (coarse + 1)) chosen (potentials (depth - (coarse + 1)))
      (Fin.cast (congrArg (fun level => (rule.generation level).vertices)
        (by omega : depth = coarse + (depth - (coarse + 1)) + 1)) vertex)
  else 0

theorem actualBlockZeroTowerStage_tail (rule : Rule) (coarse fine : ℕ)
    (chosen : Fin (rule.generation coarse).edges)
    (potentials : ∀ fine, Fin (rule.generation fine).vertices → ℝ)
    (vertex : Fin (rule.generation (coarse + fine + 1)).vertices) :
    actualBlockZeroTowerStage rule coarse chosen potentials (coarse + fine + 1) vertex =
      actualBlockZeroExtension rule coarse fine chosen (potentials fine) vertex := by
  simp only [actualBlockZeroTowerStage, dif_pos (by omega : coarse + 1 ≤ coarse + fine + 1)]
  have subtraction : coarse + fine + 1 - (coarse + 1) = fine := by omega
  exact finitePotential_apply_index_cast (fun level => (rule.generation (coarse + level + 1)).vertices)
    (fun level => actualBlockZeroExtension rule coarse level chosen (potentials level)) subtraction _ vertex

theorem actualBlockZeroTowerStage_next (rule : Rule) (coarse : ℕ)
    (chosen : Fin (rule.generation coarse).edges)
    (potentials : ∀ fine, Fin (rule.generation fine).vertices → ℝ)
    (atSource : ∀ fine, potentials fine (rule.generation fine).network.source = 0)
    (atTarget : ∀ fine, potentials fine (rule.generation fine).network.target = 0)
    (restriction : ∀ fine vertex, potentials (fine + 1) (rule.generationOldVertex fine vertex) = potentials fine vertex)
    (depth : ℕ) (vertex : Fin (rule.generation depth).vertices) :
    actualBlockZeroTowerStage rule coarse chosen potentials (depth + 1) (rule.generationOldVertex depth vertex) =
      actualBlockZeroTowerStage rule coarse chosen potentials depth vertex := by
  by_cases large : coarse + 1 ≤ depth
  · obtain ⟨fine, equality⟩ := Nat.exists_eq_add_of_le large
    have depthIdentity : depth = coarse + fine + 1 := by omega
    clear equality
    subst depth
    erw [actualBlockZeroTowerStage_tail rule coarse (fine + 1), actualBlockZeroTowerStage_tail rule coarse fine]
    exact actualBlockZeroExtension_next rule coarse fine chosen (potentials fine) (potentials (fine + 1))
      (atSource fine) (atTarget fine) (atSource (fine + 1)) (atTarget (fine + 1)) (restriction fine) vertex
  · by_cases later : coarse + 1 ≤ depth + 1
    · have depthIdentity : depth = coarse := by omega
      subst depth
      rw [actualBlockZeroTowerStage_tail rule coarse 0]
      simp only [actualBlockZeroTowerStage, dif_neg large]
      rw [← blockOldVertexEmbedding_zero rule coarse vertex, actualBlockZeroExtension_old]
    · simp only [actualBlockZeroTowerStage, dif_neg large, dif_neg later]

end
end IGSIII34.ResistanceLimit
