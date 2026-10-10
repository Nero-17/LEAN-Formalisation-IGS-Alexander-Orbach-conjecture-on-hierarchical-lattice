import Universality.Percolation.AnnealedBirthMomentSeries

namespace Universality.FiniteNetwork
noncomputable section
variable {vertices edges outerVertices outerEdges innerVertices innerEdges : ℕ}

theorem clusterFamily_size_weight (family : Finset (Finset (Fin vertices))) (weight : ℕ → ℝ) :
    (∑ size ∈ Finset.range (vertices + 1),
      weight size * ((family.filter fun cluster => cluster.card = size).card : ℝ)) =
      ∑ cluster ∈ family, weight cluster.card := by
  classical
  simp_rw [Finset.card_eq_sum_ones, Nat.cast_sum, Nat.cast_one, Finset.sum_filter,
    Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro cluster _
  have hcard : cluster.card < vertices + 1 :=
    Nat.lt_succ_of_le (by simpa using Finset.card_le_univ cluster)
  simp [hcard, eq_comm]

def expectedInternalClusterPower (R : FiniteNetwork vertices edges) (p : ℝ) (order : ℕ) : ℝ :=
  ∑ configuration, bernoulliWeight p configuration *
    ∑ cluster ∈ R.internalClusterFamily configuration, (cluster.card : ℝ) ^ order

def expectedBirthClusterPower (R : FiniteNetwork outerVertices outerEdges)
    (S : FiniteNetwork innerVertices innerEdges) (p : ℝ) (order : ℕ) : ℝ :=
  ∑ configuration : Configuration (outerEdges * innerEdges),
    bernoulliWeight p configuration *
      ∑ cluster ∈ R.birthClusterFamily S (substitutionConfigurationEquiv.symm configuration),
        (cluster.card : ℝ) ^ order

theorem sum_power_expectedInternalClusterCount (R : FiniteNetwork vertices edges)
    (p : ℝ) (order : ℕ) :
    (∑ size ∈ Finset.range (vertices + 1),
      (size : ℝ) ^ order * R.expectedInternalClusterCount p size) =
      R.expectedInternalClusterPower p order := by
  unfold expectedInternalClusterCount expectedInternalClusterPower
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro configuration _
  simp_rw [mul_left_comm ((↑_ : ℝ) ^ order) (bernoulliWeight p configuration)]
  rw [← Finset.mul_sum, ← Finset.mul_sum]
  congr 1
  simp_rw [R.internalClusterCount_eq_filter]
  exact clusterFamily_size_weight _ (fun size => (size : ℝ) ^ order)

theorem sum_power_expectedBirthClusterCount (R : FiniteNetwork outerVertices outerEdges)
    (S : FiniteNetwork innerVertices innerEdges) (p : ℝ) (order : ℕ) :
    (∑ size ∈ Finset.range (Fintype.card (R.SubstitutionVertex S) + 1),
      (size : ℝ) ^ order * R.expectedBirthClusterCount S p size) =
      R.expectedBirthClusterPower S p order := by
  unfold expectedBirthClusterCount expectedBirthClusterPower
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro configuration _
  simp_rw [mul_left_comm ((↑_ : ℝ) ^ order) (bernoulliWeight p configuration)]
  rw [← Finset.mul_sum, ← Finset.mul_sum]
  congr 1
  exact clusterFamily_size_weight _ (fun size => (size : ℝ) ^ order)

end
end Universality.FiniteNetwork

namespace Universality.Rule
noncomputable section
open scoped ENNReal

/-- Expected sum of powers of the masses of actual clusters born at one level. -/
def expectedClusterBirthPower (rule : Rule) (p : ℝ) (order : ℕ) : ℕ → ℝ
  | 0 => rule.network.expectedInternalClusterPower p order
  | generation + 1 => rule.network.expectedBirthClusterPower (rule.generation generation).network p order

theorem expectedClusterBirthPower_hasSum (rule : Rule) (p : ℝ) (order generation : ℕ) :
    HasSum (fun size : ℕ => (size : ℝ) ^ order * rule.expectedClusterBirth p size generation)
      (rule.expectedClusterBirthPower p order generation) := by
  cases generation with
  | zero =>
    change HasSum (fun size : ℕ => (size : ℝ) ^ order * rule.network.expectedInternalClusterCount p size)
      (rule.network.expectedInternalClusterPower p order)
    rw [← rule.network.sum_power_expectedInternalClusterCount p order]
    apply hasSum_sum_of_ne_finset_zero
    intro size hsize
    rw [rule.network.expectedInternalClusterCount_eq_zero p size (by
      simp only [Finset.mem_range] at hsize
      omega), mul_zero]
  | succ generation =>
    change HasSum (fun size : ℕ => (size : ℝ) ^ order *
      rule.network.expectedBirthClusterCount (rule.generation generation).network p size)
      (rule.network.expectedBirthClusterPower (rule.generation generation).network p order)
    rw [← rule.network.sum_power_expectedBirthClusterCount (rule.generation generation).network p order]
    apply hasSum_sum_of_ne_finset_zero
    intro size hsize
    rw [rule.network.expectedBirthClusterCount_eq_zero _ p size (by
      simp only [Finset.mem_range] at hsize
      omega), mul_zero]

theorem extendedBirthMoment_eq_expectation (rule : Rule)
    {p : ℝ} (hp : 0 ≤ p) (hp' : p ≤ 1) (order generation : ℕ) :
    rule.extendedBirthMoment p order generation =
      ENNReal.ofReal (rule.expectedClusterBirthPower p order generation) := by
  rw [← (rule.expectedClusterBirthPower_hasSum p order generation).tsum_eq,
    ENNReal.ofReal_tsum_of_nonneg
      (fun size => mul_nonneg (pow_nonneg (Nat.cast_nonneg _) _)
        (rule.expectedClusterBirth_bounds hp hp' size generation).1)
      (rule.expectedClusterBirthPower_hasSum p order generation).summable]
  unfold extendedBirthMoment
  apply tsum_congr
  intro size
  rw [ENNReal.ofReal_mul (pow_nonneg (Nat.cast_nonneg _) _),
    ENNReal.ofReal_pow (Nat.cast_nonneg _), ENNReal.ofReal_natCast]

theorem extendedBirthMoment_ne_top (rule : Rule)
    {p : ℝ} (hp : 0 ≤ p) (hp' : p ≤ 1) (order generation : ℕ) :
    rule.extendedBirthMoment p order generation ≠ ⊤ := by
  rw [rule.extendedBirthMoment_eq_expectation hp hp' order generation]
  exact ENNReal.ofReal_ne_top

theorem expectedClusterBirthPower_nonneg (rule : Rule)
    {p : ℝ} (hp : 0 ≤ p) (hp' : p ≤ 1) (order generation : ℕ) :
    0 ≤ rule.expectedClusterBirthPower p order generation := by
  rw [← (rule.expectedClusterBirthPower_hasSum p order generation).tsum_eq]
  exact tsum_nonneg (fun size => mul_nonneg (pow_nonneg (Nat.cast_nonneg _) _)
    (rule.expectedClusterBirth_bounds hp hp' size generation).1)

/-- The paper's birth-moment series, expressed using actual finite graph
cluster families. Valid whether the infinite series is finite or divergent. -/
theorem limitingRootSizeMoment_expected_birth_series (rule : Rule)
    (hedges : 1 < rule.edges) (hvertices : 2 < rule.vertices)
    {p : ℝ} (hp : 0 ≤ p) (hp' : p ≤ 1) (order : ℕ) :
    rule.limitingRootSizeMoment p order =
      ENNReal.ofReal (((rule.edges : ℝ) - 1) / ((rule.vertices : ℝ) - 2)) *
        ∑' generation : ℕ, ENNReal.ofReal ((1 / (rule.edges : ℝ)) ^ (generation + 1)) *
          ENNReal.ofReal (rule.expectedClusterBirthPower p (order + 1) generation) := by
  rw [rule.limitingRootSizeMoment_birth_series hedges hvertices hp hp' order]
  simp_rw [rule.extendedBirthMoment_eq_expectation hp hp']

theorem limitingRootSizeMoment_finite_iff_birth_summable (rule : Rule)
    (hedges : 1 < rule.edges) (hvertices : 2 < rule.vertices)
    {p : ℝ} (hp : 0 ≤ p) (hp' : p ≤ 1) (order : ℕ) :
    rule.limitingRootSizeMoment p order ≠ ⊤ ↔
      Summable (fun generation : ℕ => (1 / (rule.edges : ℝ)) ^ (generation + 1) *
        rule.expectedClusterBirthPower p (order + 1) generation) := by
  have hm : (1 : ℝ) < rule.edges := by exact_mod_cast hedges
  have hv : (2 : ℝ) < rule.vertices := by exact_mod_cast hvertices
  have hscale : ENNReal.ofReal (((rule.edges : ℝ) - 1) / ((rule.vertices : ℝ) - 2)) ≠ 0 :=
    (ENNReal.ofReal_pos.mpr (div_pos (sub_pos.mpr hm) (sub_pos.mpr hv))).ne'
  have hnonneg (generation : ℕ) : 0 ≤ (1 / (rule.edges : ℝ)) ^ (generation + 1) *
      rule.expectedClusterBirthPower p (order + 1) generation :=
    mul_nonneg (by positivity) (rule.expectedClusterBirthPower_nonneg hp hp' _ _)
  have hterm (generation : ℕ) :
      ENNReal.ofReal ((1 / (rule.edges : ℝ)) ^ (generation + 1)) *
        ENNReal.ofReal (rule.expectedClusterBirthPower p (order + 1) generation) =
      ENNReal.ofReal ((1 / (rule.edges : ℝ)) ^ (generation + 1) *
        rule.expectedClusterBirthPower p (order + 1) generation) :=
    (ENNReal.ofReal_mul (by positivity)).symm
  rw [rule.limitingRootSizeMoment_expected_birth_series hedges hvertices hp hp' order]
  simp_rw [hterm]
  constructor
  · intro hfinite
    have hsum := (ENNReal.lt_top_of_mul_ne_top_right hfinite hscale).ne
    have hs := (ENNReal.hasSum_toReal hsum).summable
    simpa only [ENNReal.toReal_ofReal (hnonneg _)] using hs
  · intro hs
    exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top hs.tsum_ofReal_ne_top

end
end Universality.Rule
