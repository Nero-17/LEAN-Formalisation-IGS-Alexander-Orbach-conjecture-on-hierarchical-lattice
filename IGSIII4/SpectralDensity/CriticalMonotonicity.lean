import IGSIII4.SpectralDensity.ActualCritical

/-! Strict monotonicity of the two sides of the critical equation. -/

set_option autoImplicit false

namespace IGSIII4.SpectralDensity.ActualFamily
noncomputable section

theorem chain_probability_strictMonoOn (blocks paths length : ℕ)
    (blocksPositive : 0 < blocks) (pathsPositive : 0 < paths)
    (lengthPositive : 0 < length) :
    StrictMonoOn (fun probability : ℝ =>
      (1 - (1 - probability ^ length) ^ paths) ^ blocks) (Set.Icc 0 1) := by
  intro first firstMember second secondMember ordered
  have powers : first ^ length < second ^ length :=
    pow_lt_pow_left₀ ordered firstMember.1 (by omega)
  have secondPowerAtMostOne : second ^ length ≤ 1 :=
    pow_le_one₀ secondMember.1 secondMember.2
  have firstPowerAtMostOne : first ^ length ≤ 1 := powers.le.trans secondPowerAtMostOne
  have failurePowers : (1 - second ^ length) ^ paths < (1 - first ^ length) ^ paths :=
    pow_lt_pow_left₀ (by linarith) (sub_nonneg.mpr secondPowerAtMostOne) (by omega)
  have firstFailureAtMostOne : (1 - first ^ length) ^ paths ≤ 1 :=
    pow_le_one₀ (sub_nonneg.mpr firstPowerAtMostOne)
      (by linarith [pow_nonneg firstMember.1 length])
  exact pow_lt_pow_left₀ (by linarith) (sub_nonneg.mpr firstFailureAtMostOne) (by omega)

theorem critical_reciprocal_strictAntiOn :
    StrictAntiOn (fun probability : ℝ => 1 / (probability * (1 + probability)))
      (Set.Ioi 0) := by
  intro first firstPositive second secondPositive ordered
  change 0 < first at firstPositive
  change 0 < second at secondPositive
  apply one_div_lt_one_div_of_lt (by positivity : 0 < first * (1 + first))
  have squares : first ^ 2 < second ^ 2 :=
    pow_lt_pow_left₀ ordered firstPositive.le (by norm_num)
  nlinarith

end
end IGSIII4.SpectralDensity.ActualFamily
