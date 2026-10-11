import Universality.Certificates.Opposite.Crossing00
import Universality.Certificates.Opposite.Crossing01
import Universality.Certificates.Opposite.Crossing02
import Universality.Certificates.Opposite.Crossing03
import Universality.Certificates.Opposite.Crossing04
import Universality.Certificates.Opposite.Crossing05
import Universality.Certificates.Opposite.Crossing06
import Universality.Certificates.Opposite.Crossing07
import Universality.Certificates.Opposite.Crossing08
import Universality.Certificates.Opposite.Crossing09
import Universality.Certificates.Opposite.Crossing10
import Universality.Certificates.Opposite.Crossing11
import Universality.Certificates.Opposite.Crossing12
import Universality.Certificates.Opposite.Crossing13
import Universality.Certificates.Opposite.Crossing14
import Universality.Certificates.Opposite.Crossing15
import Universality.Certificates.Opposite.Crossing16
import Universality.Certificates.Opposite.Crossing17
import Universality.Certificates.Opposite.Crossing18
import Universality.Certificates.Opposite.Crossing19
import Universality.Certificates.Opposite.Crossing20
import Universality.Certificates.Opposite.Crossing21
import Universality.Certificates.Opposite.Crossing22
import Universality.Certificates.Opposite.Crossing23
import Universality.Certificates.Opposite.Crossing24
import Universality.Certificates.Opposite.Crossing25
import Universality.Certificates.Opposite.Crossing26
import Universality.Certificates.Opposite.Crossing27
import Universality.Certificates.Opposite.Crossing28
import Universality.Certificates.Opposite.Crossing29
import Universality.Certificates.Opposite.Crossing30
import Universality.Certificates.Opposite.Crossing31
import Universality.Certificates.Opposite.Crossing32
import Universality.Certificates.Opposite.Crossing33
import Universality.Certificates.Opposite.Crossing34
import Universality.Certificates.Opposite.Crossing35
import Universality.Certificates.Opposite.Crossing36
import Universality.Certificates.Opposite.Crossing37
import Universality.Certificates.Opposite.Crossing38
import Universality.Certificates.Opposite.Crossing39
import Universality.Certificates.Opposite.Crossing40
import Universality.Certificates.Opposite.Crossing41
import Universality.Certificates.Opposite.Crossing42
import Universality.Certificates.Opposite.Crossing43
import Universality.Certificates.Opposite.Crossing44
import Universality.Certificates.Opposite.Crossing45
import Universality.Certificates.Opposite.Crossing46
import Universality.Certificates.Opposite.Crossing47
import Universality.Certificates.Opposite.Crossing48
import Universality.Certificates.Opposite.Crossing49
import Universality.Certificates.Opposite.Crossing50
import Universality.Certificates.Opposite.Crossing51
import Universality.Certificates.Opposite.Crossing52
import Universality.Certificates.Opposite.Crossing53
import Universality.Certificates.Opposite.Crossing54
import Universality.Certificates.Opposite.Crossing55
import Universality.Certificates.Opposite.Crossing56
import Universality.Certificates.Opposite.Crossing57
import Universality.Certificates.Opposite.Crossing58
import Universality.Certificates.Opposite.Crossing59
import Universality.Certificates.Opposite.Crossing60
import Universality.Certificates.Opposite.Crossing61
import Universality.Certificates.Opposite.Crossing62
import Universality.Certificates.Opposite.Crossing63
import Universality.Percolation.OppositeWheatstoneCounts
import Universality.Percolation.ReliabilityDerivative

namespace Universality
open FiniteNetwork Polynomial

def oppositeWheatstoneCrossingTable : Fin 14 → ℕ := ![0,0,0,5,54,251,660,1056,1036,661,281,78,13,1]

set_option maxHeartbeats 2000000 in
theorem oppositeWheatstone_crossing_counts_by_size (size : Fin 14) :
    oppositeWheatstoneNetwork.crossingCountBySize size.val = oppositeWheatstoneCrossingTable size := by
  rw [← certified_crossingCountBySize oppositeWheatstoneNetwork oppositeComponentRows
    oppositeComponentRows_indices oppositeComponentRows_valid]
  simp only [oppositeComponentRows, List.map_append, List.sum_append,
      oppositeRows00_crossing,
      oppositeRows01_crossing,
      oppositeRows02_crossing,
      oppositeRows03_crossing,
      oppositeRows04_crossing,
      oppositeRows05_crossing,
      oppositeRows06_crossing,
      oppositeRows07_crossing,
      oppositeRows08_crossing,
      oppositeRows09_crossing,
      oppositeRows10_crossing,
      oppositeRows11_crossing,
      oppositeRows12_crossing,
      oppositeRows13_crossing,
      oppositeRows14_crossing,
      oppositeRows15_crossing,
      oppositeRows16_crossing,
      oppositeRows17_crossing,
      oppositeRows18_crossing,
      oppositeRows19_crossing,
      oppositeRows20_crossing,
      oppositeRows21_crossing,
      oppositeRows22_crossing,
      oppositeRows23_crossing,
      oppositeRows24_crossing,
      oppositeRows25_crossing,
      oppositeRows26_crossing,
      oppositeRows27_crossing,
      oppositeRows28_crossing,
      oppositeRows29_crossing,
      oppositeRows30_crossing,
      oppositeRows31_crossing,
      oppositeRows32_crossing,
      oppositeRows33_crossing,
      oppositeRows34_crossing,
      oppositeRows35_crossing,
      oppositeRows36_crossing,
      oppositeRows37_crossing,
      oppositeRows38_crossing,
      oppositeRows39_crossing,
      oppositeRows40_crossing,
      oppositeRows41_crossing,
      oppositeRows42_crossing,
      oppositeRows43_crossing,
      oppositeRows44_crossing,
      oppositeRows45_crossing,
      oppositeRows46_crossing,
      oppositeRows47_crossing,
      oppositeRows48_crossing,
      oppositeRows49_crossing,
      oppositeRows50_crossing,
      oppositeRows51_crossing,
      oppositeRows52_crossing,
      oppositeRows53_crossing,
      oppositeRows54_crossing,
      oppositeRows55_crossing,
      oppositeRows56_crossing,
      oppositeRows57_crossing,
      oppositeRows58_crossing,
      oppositeRows59_crossing,
      oppositeRows60_crossing,
      oppositeRows61_crossing,
      oppositeRows62_crossing,
      oppositeRows63_crossing]
  fin_cases size <;> rfl

theorem oppositeWheatstone_reliabilityPolynomial :
    oppositeWheatstoneNetwork.reliabilityPolynomial = (5) * X ^ 3 + (4) * X ^ 4 + (-10) * X ^ 5 + (-4) * X ^ 6 + (-22) * X ^ 7 + (48) * X ^ 8 + (37) * X ^ 9 + (-143) * X ^ 10 + (130) * X ^ 11 + (-52) * X ^ 12 + (8) * X ^ 13 := by
  rw [reliabilityPolynomial_bernstein]
  have h0 : oppositeWheatstoneNetwork.crossingCountBySize 0 = 0 := oppositeWheatstone_crossing_counts_by_size (0 : Fin 14)
  have h1 : oppositeWheatstoneNetwork.crossingCountBySize 1 = 0 := oppositeWheatstone_crossing_counts_by_size (1 : Fin 14)
  have h2 : oppositeWheatstoneNetwork.crossingCountBySize 2 = 0 := oppositeWheatstone_crossing_counts_by_size (2 : Fin 14)
  have h3 : oppositeWheatstoneNetwork.crossingCountBySize 3 = 5 := oppositeWheatstone_crossing_counts_by_size (3 : Fin 14)
  have h4 : oppositeWheatstoneNetwork.crossingCountBySize 4 = 54 := oppositeWheatstone_crossing_counts_by_size (4 : Fin 14)
  have h5 : oppositeWheatstoneNetwork.crossingCountBySize 5 = 251 := oppositeWheatstone_crossing_counts_by_size (5 : Fin 14)
  have h6 : oppositeWheatstoneNetwork.crossingCountBySize 6 = 660 := oppositeWheatstone_crossing_counts_by_size (6 : Fin 14)
  have h7 : oppositeWheatstoneNetwork.crossingCountBySize 7 = 1056 := oppositeWheatstone_crossing_counts_by_size (7 : Fin 14)
  have h8 : oppositeWheatstoneNetwork.crossingCountBySize 8 = 1036 := oppositeWheatstone_crossing_counts_by_size (8 : Fin 14)
  have h9 : oppositeWheatstoneNetwork.crossingCountBySize 9 = 661 := oppositeWheatstone_crossing_counts_by_size (9 : Fin 14)
  have h10 : oppositeWheatstoneNetwork.crossingCountBySize 10 = 281 := oppositeWheatstone_crossing_counts_by_size (10 : Fin 14)
  have h11 : oppositeWheatstoneNetwork.crossingCountBySize 11 = 78 := oppositeWheatstone_crossing_counts_by_size (11 : Fin 14)
  have h12 : oppositeWheatstoneNetwork.crossingCountBySize 12 = 13 := oppositeWheatstone_crossing_counts_by_size (12 : Fin 14)
  have h13 : oppositeWheatstoneNetwork.crossingCountBySize 13 = 1 := oppositeWheatstone_crossing_counts_by_size (13 : Fin 14)
  norm_num [Finset.sum_range_succ, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13]
  ring

theorem oppositeWheatstone_thermal_derivative :
    oppositeWheatstoneNetwork.reliabilityPolynomial.derivative.eval₂ (Rat.castHom ℝ) (1 / 2) =
      (67 / 32 : ℝ) := by
  rw [oppositeWheatstone_reliabilityPolynomial]
  norm_num [Polynomial.derivative_mul, Polynomial.derivative_sub,
    Polynomial.derivative_add, Polynomial.derivative_X_pow]

theorem oppositeWheatstone_deriv_half :
    deriv oppositeWheatstoneNetwork.reliability (1 / 2) = 67 / 32 := by
  have h := oppositeWheatstoneNetwork.hasDerivAt_reliability (1 / 2)
  rw [oppositeWheatstone_thermal_derivative] at h
  exact h.deriv

end Universality
