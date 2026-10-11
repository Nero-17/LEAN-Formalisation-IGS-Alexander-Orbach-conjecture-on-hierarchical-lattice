import Universality.Geometry.SymbolicHausdorffLowerBound
import Mathlib.Topology.MetricSpace.HausdorffDistance

namespace Universality.Geometry.SeparatedSimilarities
noncomputable section
open Set Filter Metric
open scoped Topology ENNReal

variable {Alphabet Ambient : Type*}

def prefixMap (maps : Alphabet → Ambient → Ambient) (address : ℕ → Alphabet) : ℕ → Ambient → Ambient
  | 0 => id
  | depth + 1 => prefixMap maps address depth ∘ maps (address depth)

@[simp] theorem prefix_zero (maps : Alphabet → Ambient → Ambient) (address : ℕ → Alphabet) :
    prefixMap maps address 0 = id := rfl

@[simp] theorem prefix_succ (maps : Alphabet → Ambient → Ambient) (address : ℕ → Alphabet) (depth : ℕ) :
    prefixMap maps address (depth + 1) = prefixMap maps address depth ∘ maps (address depth) := rfl

theorem prefix_eq_of_agree (maps : Alphabet → Ambient → Ambient) (first second : ℕ → Alphabet)
    (depth : ℕ) (hagree : ∀ index < depth, first index = second index) :
    prefixMap maps first depth = prefixMap maps second depth := by
  induction depth with
  | zero => rfl
  | succ depth ih =>
    simp only [prefix_succ, ih (fun index hindex => hagree index (Nat.lt_succ_of_lt hindex)),
      hagree depth (Nat.lt_succ_self depth)]

variable [MetricSpace Ambient]

theorem prefix_dist (maps : Alphabet → Ambient → Ambient) (contraction : ℝ)
    (hdist : ∀ symbol first second, dist (maps symbol first) (maps symbol second) =
      contraction * dist first second) (address : ℕ → Alphabet) (depth : ℕ) (first second : Ambient) :
    dist (prefixMap maps address depth first) (prefixMap maps address depth second) =
      contraction ^ depth * dist first second := by
  induction depth generalizing first second with
  | zero => simp
  | succ depth ih =>
    simp only [prefix_succ, Function.comp_apply, ih, hdist, pow_succ, mul_assoc]

theorem prefix_continuous (maps : Alphabet → Ambient → Ambient)
    (hcontinuous : ∀ symbol, Continuous (maps symbol)) (address : ℕ → Alphabet) (depth : ℕ) :
    Continuous (prefixMap maps address depth) := by
  induction depth with
  | zero => exact continuous_id
  | succ depth ih => exact ih.comp (hcontinuous _)

variable [CompactSpace Ambient] [Nonempty Ambient]

theorem exists_coding (maps : Alphabet → Ambient → Ambient)
    (hcontinuous : ∀ symbol, Continuous (maps symbol)) :
    ∃ coding : (ℕ → Alphabet) → Ambient, ∀ address depth,
      coding address ∈ Set.range (prefixMap maps address depth) := by
  have hexists (address : ℕ → Alphabet) :
      ∃ point : Ambient, ∀ depth, point ∈ Set.range (prefixMap maps address depth) := by
    have hcompact (depth : ℕ) : IsCompact (Set.range (prefixMap maps address depth)) :=
      isCompact_range (prefix_continuous maps hcontinuous address depth)
    obtain ⟨point, hpoint⟩ :=
      IsCompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed
        (fun depth => Set.range (prefixMap maps address depth))
        (fun depth => Set.range_comp_subset_range _ _)
        (fun _ => Set.range_nonempty _) (hcompact 0) (fun depth => (hcompact depth).isClosed)
    exact ⟨point, Set.mem_iInter.mp hpoint⟩
  choose coding hcoding using hexists
  exact ⟨coding, hcoding⟩

omit [CompactSpace Ambient] [Nonempty Ambient] in
/-- Membership in every nested prefix image gives quantitative separation at
exactly the first different symbol. -/
theorem coding_separation (maps : Alphabet → Ambient → Ambient) (contraction gap : ℝ)
    (hcontraction : 0 ≤ contraction)
    (hdist : ∀ symbol first second, dist (maps symbol first) (maps symbol second) =
      contraction * dist first second)
    (hseparation : ∀ first second : Alphabet, first ≠ second → ∀ x y : Ambient,
      gap ≤ dist (maps first x) (maps second y))
    (coding : (ℕ → Alphabet) → Ambient)
    (hcoding : ∀ address depth, coding address ∈ Set.range (prefixMap maps address depth))
    (first second : ℕ → Alphabet) (hne : first ≠ second) :
    gap * contraction ^ PiNat.firstDiff first second ≤ dist (coding first) (coding second) := by
  obtain ⟨x, hx⟩ := hcoding first (PiNat.firstDiff first second + 1)
  obtain ⟨y, hy⟩ := hcoding second (PiNat.firstDiff first second + 1)
  have hprefix := prefix_eq_of_agree maps first second (PiNat.firstDiff first second)
    (fun _ hindex => PiNat.apply_eq_of_lt_firstDiff hindex)
  rw [← hx, ← hy, prefix_succ, prefix_succ, Function.comp_apply, Function.comp_apply,
    ← hprefix, prefix_dist maps contraction hdist]
  simpa only [mul_comm gap] using mul_le_mul_of_nonneg_left
    (hseparation (first _) (second _) (PiNat.apply_firstDiff_ne hne) x y)
    (pow_nonneg hcontraction _)

/-- A compact metric space containing separated similarities has at least
the corresponding similarity dimension. Surjectivity of the coding is not
needed for this lower bound. -/
theorem logarithmic_dimension_le (branching : ℕ) [NeZero branching]
    (hbranching : 1 < branching) (maps : Fin branching → Ambient → Ambient)
    (contraction gap : ℝ) (hcontraction : 0 < contraction)
    (hcontraction_lt_one : contraction < 1) (hgap : 0 < gap)
    (hdist : ∀ symbol first second, dist (maps symbol first) (maps symbol second) =
      contraction * dist first second)
    (hseparation : ∀ first second : Fin branching, first ≠ second → ∀ x y : Ambient,
      gap ≤ dist (maps first x) (maps second y)) :
    ENNReal.ofReal (Real.log (branching : ℝ) / (-Real.log contraction)) ≤
      dimH (Set.univ : Set Ambient) := by
  have hcontinuous (symbol : Fin branching) : Continuous (maps symbol) := by
    have hlipschitz : LipschitzWith ⟨contraction, hcontraction.le⟩ (maps symbol) :=
      LipschitzWith.of_dist_le_mul (fun first second => le_of_eq (hdist symbol first second))
    exact hlipschitz.continuous
  obtain ⟨coding, hcoding⟩ := exists_coding maps hcontinuous
  exact (SymbolicHausdorff.logarithmic_dimension_le_of_separation branching hbranching
    coding gap contraction hgap hcontraction hcontraction_lt_one
    (coding_separation maps contraction gap hcontraction.le hdist hseparation coding hcoding)).trans
      (dimH_mono (Set.subset_univ _))
end
end Universality.Geometry.SeparatedSimilarities
