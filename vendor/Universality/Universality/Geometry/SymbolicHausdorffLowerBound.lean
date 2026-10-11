import Mathlib.Topology.MetricSpace.PiNat
import Mathlib.Topology.MetricSpace.HausdorffDimension
import Mathlib.Probability.ProductMeasure
import Mathlib.Probability.Distributions.Uniform

/-!
Symbolic Hausdorff lower bounds and their transport through a quantitatively
separated coding. No graph realization or degree estimate is assumed here;
applications must supply the separation inequality for their actual coding.
-/
namespace Universality.Geometry.SymbolicHausdorff
noncomputable section
open Set Filter MeasureTheory MeasureTheory.Measure Metric
open scoped Topology ENNReal NNReal

variable (branching : ℕ) [NeZero branching]
local instance : MetricSpace (ℕ → Fin branching) := PiNat.metricSpace

def uniformMeasure : Measure (ℕ → Fin branching) :=
  Measure.infinitePi (fun _ : ℕ => (PMF.uniformOfFintype (Fin branching)).toMeasure)

instance : IsProbabilityMeasure (uniformMeasure branching) := by
  unfold uniformMeasure
  infer_instance

theorem cylinder_measure (point : ℕ → Fin branching) (depth : ℕ) :
    uniformMeasure branching (PiNat.cylinder point depth) = (branching : ℝ≥0∞)⁻¹ ^ depth := by
  rw [uniformMeasure, PiNat.cylinder_eq_pi, Measure.infinitePi_pi]
  · simp
  · intro index _
    exact measurableSet_singleton _

theorem singleton_measure (hbranching : 1 < branching) (point : ℕ → Fin branching) :
    uniformMeasure branching {point} = 0 := by
  have hratio : (branching : ℝ≥0∞)⁻¹ < 1 := by
    have hcast : (1 : ℝ≥0∞) < branching := by exact_mod_cast hbranching
    simpa only [inv_one] using ENNReal.inv_lt_inv.mpr hcast
  apply le_antisymm _ bot_le
  apply ge_of_tendsto (ENNReal.tendsto_pow_atTop_nhds_zero_of_lt_one hratio)
  filter_upwards [] with depth
  rw [← cylinder_measure branching point depth]
  exact measure_mono (singleton_subset_iff.mpr (PiNat.self_mem_cylinder point depth))

omit [NeZero branching] in
theorem cylinder_mass_eq_diameter_power (hbranching : 1 < branching) (depth : ℕ) :
    (branching : ℝ≥0∞)⁻¹ ^ depth =
      ENNReal.ofReal ((1 / 2 : ℝ) ^ depth) ^
        (Real.log (branching : ℝ) / Real.log 2) := by
  have hpositive : 0 < (branching : ℝ) := by exact_mod_cast (lt_trans Nat.zero_lt_one hbranching)
  have hlog : Real.log (1 / 2 : ℝ) * (Real.log (branching : ℝ) / Real.log 2) =
      -Real.log (branching : ℝ) := by
    rw [one_div, Real.log_inv]
    field_simp [ne_of_gt (Real.log_pos (show (1 : ℝ) < 2 by norm_num))]
  have hbase : (1 / 2 : ℝ) ^ (Real.log (branching : ℝ) / Real.log 2) =
      (branching : ℝ)⁻¹ := by
    rw [Real.rpow_def_of_pos (by norm_num), hlog, Real.exp_neg, Real.exp_log hpositive]
  have hbaseENNReal : ENNReal.ofReal (1 / 2 : ℝ) ^
      (Real.log (branching : ℝ) / Real.log 2) = (branching : ℝ≥0∞)⁻¹ := by
    rw [ENNReal.ofReal_rpow_of_pos (show (0 : ℝ) < 1 / 2 by norm_num), hbase,
      ENNReal.ofReal_inv_of_pos hpositive, ENNReal.ofReal_natCast]
  rw [ENNReal.ofReal_pow (show (0 : ℝ) ≤ 1 / 2 by norm_num),
    ← ENNReal.rpow_natCast_mul, mul_comm (depth : ℝ),
    ENNReal.rpow_mul_natCast, hbaseENNReal]

/-- A uniform symbolic product measure is controlled by the exact diameter
power. The proof uses the least first-difference index in a nonsingleton set,
so it requires no estimate for balls in the eventual graph limit. -/
theorem measure_le_diameter_power (hbranching : 1 < branching)
    (set : Set (ℕ → Fin branching)) :
    uniformMeasure branching set ≤
      ediam set ^ (Real.log (branching : ℝ) / Real.log 2) := by
  classical
  have hdimension : 0 ≤ Real.log (branching : ℝ) / Real.log 2 :=
    div_nonneg (Real.log_nonneg (by exact_mod_cast (le_of_lt hbranching)))
      (Real.log_nonneg (by norm_num))
  by_cases hsubsingleton : set.Subsingleton
  · obtain rfl | ⟨point, rfl⟩ := hsubsingleton.eq_empty_or_singleton
    · simp
    · rw [singleton_measure branching hbranching]
      exact bot_le
  · have hexists : ∃ depth : ℕ, ∃ first ∈ set, ∃ second ∈ set,
        first ≠ second ∧ PiNat.firstDiff first second = depth := by
      obtain ⟨first, hfirst, second, hsecond, hne⟩ := Set.not_subsingleton_iff.mp hsubsingleton
      exact ⟨PiNat.firstDiff first second, first, hfirst, second, hsecond, hne, rfl⟩
    obtain ⟨first, hfirst, second, hsecond, hne, hdepth⟩ := Nat.find_spec hexists
    have hsubset : set ⊆ PiNat.cylinder first (Nat.find hexists) := by
      intro point hpoint
      by_cases hequal : point = first
      · subst point
        exact PiNat.self_mem_cylinder _ _
      · apply (PiNat.mem_cylinder_iff_le_firstDiff hequal _).mpr
        exact Nat.find_min' hexists ⟨point, hpoint, first, hfirst, hequal, rfl⟩
    have hdiameter : ENNReal.ofReal ((1 / 2 : ℝ) ^ Nat.find hexists) ≤ ediam set := by
      have hbound := edist_le_ediam_of_mem hfirst hsecond
      rw [edist_dist] at hbound
      rw [PiNat.dist_eq_of_ne hne, hdepth] at hbound
      exact hbound
    calc
      _ ≤ uniformMeasure branching (PiNat.cylinder first (Nat.find hexists)) := measure_mono hsubset
      _ = _ := cylinder_measure branching first _
      _ = _ := cylinder_mass_eq_diameter_power branching hbranching _
      _ ≤ _ := ENNReal.rpow_le_rpow hdiameter hdimension

/-- The uniform product measure gives the sharp symbolic Hausdorff lower
bound for the first-difference metric. -/
theorem logarithmic_dimension_le (hbranching : 1 < branching) :
    ENNReal.ofReal (Real.log (branching : ℝ) / Real.log 2) ≤
      dimH (Set.univ : Set (ℕ → Fin branching)) := by
  have hdimension : 0 ≤ Real.log (branching : ℝ) / Real.log 2 :=
    div_nonneg (Real.log_nonneg (by exact_mod_cast (le_of_lt hbranching)))
      (Real.log_nonneg (by norm_num))
  have hmeasure := Measure.le_hausdorffMeasure
    (Real.log (branching : ℝ) / Real.log 2) (uniformMeasure branching) 1 (by norm_num)
    (fun set _ => measure_le_diameter_power branching hbranching set)
  have hnonzero : Measure.hausdorffMeasure
      (Real.log (branching : ℝ) / Real.log 2) (Set.univ : Set (ℕ → Fin branching)) ≠ 0 := by
    intro hzero
    have hmass := hmeasure Set.univ
    simp only [measure_univ, hzero, nonpos_iff_eq_zero, one_ne_zero] at hmass
  have hbound := le_dimH_of_hausdorffMeasure_ne_zero
    (d := ⟨Real.log (branching : ℝ) / Real.log 2, hdimension⟩) hnonzero
  rw [ENNReal.ofReal_eq_coe_nnreal hdimension]
  exact hbound

theorem dimension_bound_of_inverse_holder {Ambient : Type*} [MetricSpace Ambient]
    (hbranching : 1 < branching) (coding : (ℕ → Fin branching) → Ambient)
    (hinjective : Function.Injective coding) (coefficient exponent : ℝ≥0)
    (hexponent : 0 < exponent)
    (hbound : ∀ first second : ℕ → Fin branching,
      dist first second ≤ coefficient * dist (coding first) (coding second) ^ (exponent : ℝ)) :
    ENNReal.ofReal (Real.log (branching : ℝ) / Real.log 2) * (exponent : ℝ≥0∞) ≤
      dimH (Set.range coding) := by
  have hleft := Function.leftInverse_invFun hinjective
  have hholder : HolderOnWith coefficient exponent (Function.invFun coding) (Set.range coding) := by
    rintro _ ⟨first, rfl⟩ _ ⟨second, rfl⟩
    rw [hleft first, hleft second]
    simpa only [edist_dist, ENNReal.coe_nnreal_eq,
      ENNReal.ofReal_rpow_of_nonneg dist_nonneg exponent.coe_nonneg,
      ← ENNReal.ofReal_mul coefficient.coe_nonneg] using
        ENNReal.ofReal_le_ofReal (hbound first second)
  have hrange : Function.invFun coding '' Set.range coding = Set.univ := by
    apply Set.eq_univ_iff_forall.mpr
    intro point
    exact ⟨coding point, Set.mem_range_self point, hleft point⟩
  have hdimension := hholder.dimH_image_le hexponent
  rw [hrange] at hdimension
  have hquotient := (logarithmic_dimension_le branching hbranching).trans hdimension
  exact (ENNReal.le_div_iff_mul_le
    (Or.inl (ENNReal.coe_ne_zero.mpr (ne_of_gt hexponent)))
    (Or.inl ENNReal.coe_ne_top)).mp hquotient

/-- A separated coding transfers symbolic dimension to its geometric image. -/
theorem dimension_bound_of_separation_power {Ambient : Type*} [MetricSpace Ambient]
    (hbranching : 1 < branching) (coding : (ℕ → Fin branching) → Ambient)
    (gap contraction : ℝ) (hgap : 0 < gap) (hcontraction : 0 < contraction)
    (exponent : ℝ≥0) (hexponent : 0 < exponent)
    (hpower : contraction ^ (exponent : ℝ) = 1 / 2)
    (hseparation : ∀ first second : ℕ → Fin branching, first ≠ second →
      gap * contraction ^ PiNat.firstDiff first second ≤ dist (coding first) (coding second)) :
    ENNReal.ofReal (Real.log (branching : ℝ) / Real.log 2) * (exponent : ℝ≥0∞) ≤
      dimH (Set.range coding) := by
  have hinjective : Function.Injective coding := by
    intro first second hequal
    by_contra hne
    have hbound := hseparation first second hne
    rw [hequal, dist_self] at hbound
    exact (not_le_of_gt (mul_pos hgap (pow_pos hcontraction _))) hbound
  let coefficient : ℝ≥0 := ⟨(gap ^ (exponent : ℝ))⁻¹, by positivity⟩
  apply dimension_bound_of_inverse_holder branching hbranching coding hinjective
    coefficient exponent hexponent
  intro first second
  by_cases hequal : first = second
  · subst second
    simp only [dist_self]
    positivity
  · rw [PiNat.dist_eq_of_ne hequal]
    have hbound := Real.rpow_le_rpow
      (le_of_lt (mul_pos hgap (pow_pos hcontraction _)))
      (hseparation first second hequal) exponent.coe_nonneg
    rw [Real.mul_rpow hgap.le (pow_nonneg hcontraction.le _),
      ← Real.rpow_pow_comm hcontraction.le, hpower] at hbound
    have hpositive : 0 < gap ^ (exponent : ℝ) := Real.rpow_pos_of_pos hgap _
    change _ ≤ (gap ^ (exponent : ℝ))⁻¹ * _
    calc
      _ = (gap ^ (exponent : ℝ))⁻¹ *
          (gap ^ (exponent : ℝ) * (1 / 2 : ℝ) ^ PiNat.firstDiff first second) := by
        field_simp
      _ ≤ _ := mul_le_mul_of_nonneg_left hbound (inv_nonneg.mpr hpositive.le)

/-- Quantitative first-difference separation gives the logarithmic Hausdorff
lower bound without a graph-degree assumption. -/
theorem logarithmic_dimension_le_of_separation {Ambient : Type*} [MetricSpace Ambient]
    (hbranching : 1 < branching) (coding : (ℕ → Fin branching) → Ambient)
    (gap contraction : ℝ) (hgap : 0 < gap) (hcontraction : 0 < contraction)
    (hcontraction_lt_one : contraction < 1)
    (hseparation : ∀ first second : ℕ → Fin branching, first ≠ second →
      gap * contraction ^ PiNat.firstDiff first second ≤ dist (coding first) (coding second)) :
    ENNReal.ofReal (Real.log (branching : ℝ) / (-Real.log contraction)) ≤
      dimH (Set.range coding) := by
  have hlogTwo : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlogContraction : 0 < -Real.log contraction :=
    neg_pos.mpr (Real.log_neg hcontraction hcontraction_lt_one)
  let exponent : ℝ≥0 := ⟨Real.log 2 / (-Real.log contraction),
    le_of_lt (div_pos hlogTwo hlogContraction)⟩
  have hexponent : 0 < exponent := div_pos hlogTwo hlogContraction
  have hpower : contraction ^ (exponent : ℝ) = 1 / 2 := by
    rw [Real.rpow_def_of_pos hcontraction]
    have hproduct : Real.log contraction * (exponent : ℝ) = -Real.log 2 := by
      change Real.log contraction * (Real.log 2 / (-Real.log contraction)) = -Real.log 2
      field_simp [ne_of_lt (Real.log_neg hcontraction hcontraction_lt_one)]
    rw [hproduct, Real.exp_neg, Real.exp_log (by norm_num : (0 : ℝ) < 2)]
    norm_num
  have hbound := dimension_bound_of_separation_power branching hbranching coding gap contraction
    hgap hcontraction exponent hexponent hpower hseparation
  have hdimension : 0 ≤ Real.log (branching : ℝ) / Real.log 2 :=
    div_nonneg (Real.log_nonneg (by exact_mod_cast (le_of_lt hbranching))) hlogTwo.le
  rw [ENNReal.coe_nnreal_eq, ← ENNReal.ofReal_mul hdimension] at hbound
  have hidentity : (Real.log (branching : ℝ) / Real.log 2) * (exponent : ℝ) =
      Real.log (branching : ℝ) / (-Real.log contraction) := by
    change (Real.log (branching : ℝ) / Real.log 2) *
      (Real.log 2 / (-Real.log contraction)) = _
    field_simp [hlogTwo.ne', ne_of_lt (Real.log_neg hcontraction hcontraction_lt_one)]
  rw [hidentity] at hbound
  exact hbound
end
end Universality.Geometry.SymbolicHausdorff
