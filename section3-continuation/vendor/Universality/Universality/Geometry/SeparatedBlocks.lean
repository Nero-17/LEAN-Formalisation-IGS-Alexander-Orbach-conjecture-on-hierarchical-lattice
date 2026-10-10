import Universality.Geometry.SeparatedSimilarities
import Universality.Geometry.BlockDimensionLimit
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.EquivFin

/-! Finite blocks ending in one interior copy give separated similarities.
The height and separation assumptions are quantitative inequalities on the
actual ambient metric; no Hausdorff dimension formula is assumed. -/

namespace Universality.Geometry.SeparatedBlocks
noncomputable section
open Set Metric
open scoped ENNReal

variable {Alphabet Ambient : Type*}

/-- A finite word acts from its first symbol to its last symbol. -/
def wordMap (maps : Alphabet → Ambient → Ambient) :
    (depth : ℕ) → (Fin depth → Alphabet) → Ambient → Ambient
  | 0, _ => id
  | depth + 1, word => maps (word 0) ∘ wordMap maps depth (fun index => word index.succ)

@[simp] theorem wordMap_zero (maps : Alphabet → Ambient → Ambient)
    (word : Fin 0 → Alphabet) : wordMap maps 0 word = id := rfl

@[simp] theorem wordMap_succ (maps : Alphabet → Ambient → Ambient) (depth : ℕ)
    (word : Fin (depth + 1) → Alphabet) :
    wordMap maps (depth + 1) word =
      maps (word 0) ∘ wordMap maps depth (fun index => word index.succ) := rfl

variable [MetricSpace Ambient]

theorem wordMap_dist (maps : Alphabet → Ambient → Ambient) (contraction : ℝ)
    (hdist : ∀ symbol first second,
      dist (maps symbol first) (maps symbol second) = contraction * dist first second)
    (depth : ℕ) (word : Fin depth → Alphabet) (first second : Ambient) :
    dist (wordMap maps depth word first) (wordMap maps depth word second) =
      contraction ^ depth * dist first second := by
  induction depth with
  | zero => simp
  | succ depth ih =>
    simp only [wordMap_succ, Function.comp_apply, hdist, ih, pow_succ]
    ring

omit [MetricSpace Ambient] in
theorem wordMap_height (maps : Alphabet → Ambient → Ambient)
    (height : Ambient → ℝ) (contraction : ℝ) (hcontraction : 0 ≤ contraction)
    (hheight : ∀ symbol point, contraction * height point ≤ height (maps symbol point))
    (depth : ℕ) (word : Fin depth → Alphabet) (point : Ambient) :
    contraction ^ depth * height point ≤ height (wordMap maps depth word point) := by
  induction depth with
  | zero => simp
  | succ depth ih =>
    simp only [wordMap_succ, Function.comp_apply]
    calc
      contraction ^ (depth + 1) * height point =
          contraction * (contraction ^ depth * height point) := by rw [pow_succ]; ring
      _ ≤ contraction * height (wordMap maps depth (fun index => word index.succ) point) :=
        mul_le_mul_of_nonneg_left (ih _) hcontraction
      _ ≤ _ := hheight _ _

/-- Distinct words of the same length separate all points of the interior copy.
No positivity hypothesis on height outside the copy is needed. -/
theorem wordMap_internal_separation (maps : Alphabet → Ambient → Ambient)
    (height : Ambient → ℝ) (contraction gap : ℝ) (hcontraction : 0 ≤ contraction)
    (hdist : ∀ symbol first second,
      dist (maps symbol first) (maps symbol second) = contraction * dist first second)
    (hheight : ∀ symbol point, contraction * height point ≤ height (maps symbol point))
    (hcross : ∀ first second : Alphabet, first ≠ second → ∀ x y : Ambient,
      contraction * (height x + height y) ≤ dist (maps first x) (maps second y))
    (internal : Ambient → Ambient) (hinternal : ∀ point, gap ≤ height (internal point))
    (depth : ℕ) (first second : Fin depth → Alphabet) (hne : first ≠ second)
    (x y : Ambient) :
    2 * gap * contraction ^ depth ≤
      dist (wordMap maps depth first (internal x)) (wordMap maps depth second (internal y)) := by
  induction depth with
  | zero => exact (hne (Subsingleton.elim _ _)).elim
  | succ depth ih =>
    simp only [wordMap_succ, Function.comp_apply]
    by_cases hhead : first 0 = second 0
    · have htail : (fun index : Fin depth => first index.succ) ≠
          (fun index : Fin depth => second index.succ) := by
        intro heq
        apply hne
        funext index
        exact Fin.cases hhead (fun index => congrFun heq index) index
      rw [hhead, hdist]
      calc
        2 * gap * contraction ^ (depth + 1) =
            contraction * (2 * gap * contraction ^ depth) := by rw [pow_succ]; ring
        _ ≤ _ := mul_le_mul_of_nonneg_left (ih _ _ htail) hcontraction
    · have hfirst : contraction ^ depth * gap ≤
          height (wordMap maps depth (fun index => first index.succ) (internal x)) :=
        (mul_le_mul_of_nonneg_left (hinternal x) (pow_nonneg hcontraction depth)).trans
          (wordMap_height maps height contraction hcontraction hheight _ _ _)
      have hsecond : contraction ^ depth * gap ≤
          height (wordMap maps depth (fun index => second index.succ) (internal y)) :=
        (mul_le_mul_of_nonneg_left (hinternal y) (pow_nonneg hcontraction depth)).trans
          (wordMap_height maps height contraction hcontraction hheight _ _ _)
      calc
        2 * gap * contraction ^ (depth + 1) =
            contraction * (contraction ^ depth * gap + contraction ^ depth * gap) := by
          rw [pow_succ]; ring
        _ ≤ contraction *
            (height (wordMap maps depth (fun index => first index.succ) (internal x)) +
             height (wordMap maps depth (fun index => second index.succ) (internal y))) :=
          mul_le_mul_of_nonneg_left (add_le_add hfirst hsecond) hcontraction
        _ ≤ _ := hcross _ _ hhead _ _

variable [CompactSpace Ambient] [Nonempty Ambient]

/-- Every positive block length gives a lower Hausdorff bound. The fixed
interior copy costs only `internalDepth` extra contractions. -/
theorem logarithmic_dimension_le (branching depth internalDepth : ℕ)
    (hbranching : 1 < branching) (hdepth : 0 < depth)
    (maps : Fin branching → Ambient → Ambient) (height : Ambient → ℝ)
    (contraction gap : ℝ) (hcontraction : 0 < contraction)
    (hcontraction_lt_one : contraction < 1) (hgap : 0 < gap)
    (hdist : ∀ symbol first second,
      dist (maps symbol first) (maps symbol second) = contraction * dist first second)
    (hheight : ∀ symbol point, contraction * height point ≤ height (maps symbol point))
    (hcross : ∀ first second : Fin branching, first ≠ second → ∀ x y : Ambient,
      contraction * (height x + height y) ≤ dist (maps first x) (maps second y))
    (internal : Ambient → Ambient)
    (hinternal_dist : ∀ first second,
      dist (internal first) (internal second) =
        contraction ^ internalDepth * dist first second)
    (hinternal_height : ∀ point, gap ≤ height (internal point)) :
    ENNReal.ofReal (Real.log ((branching ^ depth : ℕ) : ℝ) /
      (-Real.log (contraction ^ (depth + internalDepth)))) ≤
      dimH (Set.univ : Set Ambient) := by
  let words : Fin (branching ^ depth) ≃ (Fin depth → Fin branching) :=
    (Fintype.equivFinOfCardEq (by simp)).symm
  let blockMaps (symbol : Fin (branching ^ depth)) : Ambient → Ambient :=
    wordMap maps depth (words symbol) ∘ internal
  have hbranching_pow : 1 < branching ^ depth := one_lt_pow₀ hbranching (Nat.ne_of_gt hdepth)
  letI : NeZero (branching ^ depth) := ⟨Nat.ne_of_gt (lt_trans Nat.zero_lt_one hbranching_pow)⟩
  apply SeparatedSimilarities.logarithmic_dimension_le (branching ^ depth) hbranching_pow
    blockMaps (contraction ^ (depth + internalDepth)) (2 * gap * contraction ^ depth)
    (pow_pos hcontraction _) (pow_lt_one₀ hcontraction.le hcontraction_lt_one (by omega))
    (mul_pos (mul_pos (by norm_num) hgap) (pow_pos hcontraction _))
  · intro symbol first second
    dsimp [blockMaps]
    rw [wordMap_dist maps contraction hdist, hinternal_dist, pow_add]
    ring
  · intro first second hne x y
    exact wordMap_internal_separation maps height contraction gap hcontraction.le
      hdist hheight hcross internal hinternal_height depth (words first) (words second)
      (fun heq => hne (words.injective heq)) x y

/-- The block bound in the integer scale convention used by graph substitution. -/
theorem integer_scale_block_dimension_le (branching scale depth internalDepth : ℕ)
    (hbranching : 1 < branching) (hscale : 1 < scale) (hdepth : 0 < depth)
    (maps : Fin branching → Ambient → Ambient) (height : Ambient → ℝ)
    (gap : ℝ) (hgap : 0 < gap)
    (hdist : ∀ symbol first second,
      dist (maps symbol first) (maps symbol second) =
        (1 / (scale : ℝ)) * dist first second)
    (hheight : ∀ symbol point,
      (1 / (scale : ℝ)) * height point ≤ height (maps symbol point))
    (hcross : ∀ first second : Fin branching, first ≠ second → ∀ x y : Ambient,
      (1 / (scale : ℝ)) * (height x + height y) ≤ dist (maps first x) (maps second y))
    (internal : Ambient → Ambient)
    (hinternal_dist : ∀ first second,
      dist (internal first) (internal second) =
        (1 / (scale : ℝ)) ^ internalDepth * dist first second)
    (hinternal_height : ∀ point, gap ≤ height (internal point)) :
    ENNReal.ofReal ((depth : ℝ) * Real.log (branching : ℝ) /
      ((depth + internalDepth : ℕ) * Real.log (scale : ℝ))) ≤
      dimH (Set.univ : Set Ambient) := by
  have hscale_real : (1 : ℝ) < scale := by exact_mod_cast hscale
  have hpositive : 0 < (1 / (scale : ℝ)) := one_div_pos.mpr (by linarith)
  have hlt : (1 / (scale : ℝ)) < 1 := by
    simpa only [one_div] using (inv_lt_one₀ (by linarith)).mpr hscale_real
  simpa only [Nat.cast_pow, Real.log_pow, one_div, Real.log_inv, mul_neg, neg_neg] using
    logarithmic_dimension_le branching depth internalDepth hbranching hdepth maps height
      (1 / (scale : ℝ)) gap hpositive hlt hgap hdist hheight hcross internal
      hinternal_dist hinternal_height

/-- Interior copies of fixed depth and the boundary inequalities imply the full
similarity-dimension lower bound, by letting the free block length tend to infinity. -/
theorem integer_scale_dimension_le (branching scale internalDepth : ℕ)
    (hbranching : 1 < branching) (hscale : 1 < scale)
    (maps : Fin branching → Ambient → Ambient) (height : Ambient → ℝ)
    (gap : ℝ) (hgap : 0 < gap)
    (hdist : ∀ symbol first second,
      dist (maps symbol first) (maps symbol second) =
        (1 / (scale : ℝ)) * dist first second)
    (hheight : ∀ symbol point,
      (1 / (scale : ℝ)) * height point ≤ height (maps symbol point))
    (hcross : ∀ first second : Fin branching, first ≠ second → ∀ x y : Ambient,
      (1 / (scale : ℝ)) * (height x + height y) ≤ dist (maps first x) (maps second y))
    (internal : Ambient → Ambient)
    (hinternal_dist : ∀ first second,
      dist (internal first) (internal second) =
        (1 / (scale : ℝ)) ^ internalDepth * dist first second)
    (hinternal_height : ∀ point, gap ≤ height (internal point)) :
    ENNReal.ofReal (Real.log (branching : ℝ) / Real.log (scale : ℝ)) ≤
      dimH (Set.univ : Set Ambient) := by
  apply Universality.logarithmic_dimension_le_of_block_bounds branching scale internalDepth
  intro depth hdepth
  exact integer_scale_block_dimension_le branching scale depth internalDepth hbranching
    hscale hdepth maps height gap hgap hdist hheight hcross internal
    hinternal_dist hinternal_height

end
end Universality.Geometry.SeparatedBlocks

