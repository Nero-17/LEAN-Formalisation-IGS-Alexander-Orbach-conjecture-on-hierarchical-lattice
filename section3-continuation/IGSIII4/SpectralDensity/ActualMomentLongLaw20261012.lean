import IGSIII4.SpectralDensity.ActualMomentActualBlock20261012
import IGSIII4.SpectralDensity.ActualMomentIndependentSum20261012

set_option autoImplicit false
set_option maxHeartbeats 0
set_option backward.isDefEq.respectTransparency false

namespace IGSIII4.SpectralDensity.ActualFamily
noncomputable section
open scoped BigOperators
open Universality Universality.FiniteNetwork IGSIII34.Probability
attribute [local instance] Classical.propDecidable

abbrev BlockSample (paths length : ℕ) (Outcome : Type*) :=
  (Fin paths → Configuration length) × (Fin paths → Fin length → Outcome)

def actualBlockJointWeight {Outcome : Type*} [Fintype Outcome] [Nonempty Outcome]
    (paths length : ℕ) (probability : ℝ) (weight : Outcome → ℝ)
    (sample : BlockSample paths length Outcome) : ℝ :=
  conditionalActualBlockWeight paths length probability sample.1 * blockProductWeight weight sample.2

def actualBlockSampleResponse {Outcome : Type*} (paths length : ℕ)
    (response : Outcome → ℝ) (sample : BlockSample paths length Outcome) : ℝ :=
  blockInputResponse (pathStatuses paths length sample.1) response sample.2

theorem conditionalActualBlockWeight_normalized20261012 (paths length : ℕ) (probability : ℝ)
    (crossingPositive : 0 < 1 - (1 - probability ^ length) ^ paths) :
    (∑ configuration, conditionalActualBlockWeight paths length probability configuration) = 1 := by
  have identity := conditional_actual_block_status_law20261012 paths length probability (fun _ => 1)
  rw [finiteMean_const _ (conditionalStatusWeight_normalized paths _ crossingPositive)] at identity
  simpa only [finiteMean, mul_one] using identity

theorem actualBlockJointWeight_normalized20261012 {Outcome : Type*} [Fintype Outcome] [Nonempty Outcome]
    (paths length : ℕ) (probability : ℝ) (crossingPositive : 0 < 1 - (1 - probability ^ length) ^ paths)
    (weight : Outcome → ℝ) (normalized : ∑ outcome, weight outcome = 1) :
    (∑ sample, actualBlockJointWeight paths length probability weight sample) = 1 :=
  product_weight_normalized _ _ (conditionalActualBlockWeight_normalized20261012 paths length probability crossingPositive)
    (blockProductWeight_normalized20261012 weight normalized)

theorem actualBlockSample_observable20261012 {Outcome : Type*} [Fintype Outcome] [Nonempty Outcome]
    (paths length : ℕ) (probability : ℝ) (weight response : Outcome → ℝ) (observable : ℝ → ℝ) :
    finiteMean (actualBlockJointWeight paths length probability weight)
      (fun sample => observable (actualBlockSampleResponse paths length response sample)) =
        actualBlockObservable paths length probability weight response observable :=
  finiteMean_product (conditionalActualBlockWeight paths length probability) (blockProductWeight weight)
    (fun configuration input => observable (blockInputResponse (pathStatuses paths length configuration) response input))

abbrev LongSample (blocks paths length : ℕ) (Outcome : Type*) :=
  (Outcome × Outcome) × (Fin blocks → BlockSample paths length Outcome)

def actualLongWeight {Outcome : Type*} [Fintype Outcome] [Nonempty Outcome]
    (blocks paths length : ℕ) (probability : ℝ) (weight : Outcome → ℝ)
    (sample : LongSample blocks paths length Outcome) : ℝ :=
  (weight sample.1.1 * weight sample.1.2) *
    productWeight (actualBlockJointWeight paths length probability weight) sample.2

def actualLongResponse {Outcome : Type*} (blocks paths length : ℕ)
    (response : Outcome → ℝ) (sample : LongSample blocks paths length Outcome) : ℝ :=
  (response sample.1.1 + response sample.1.2) +
    ∑ block, actualBlockSampleResponse paths length response (sample.2 block)

theorem actualLongWeight_normalized20261012 {Outcome : Type*} [Fintype Outcome] [Nonempty Outcome]
    (blocks paths length : ℕ) (probability : ℝ) (crossingPositive : 0 < 1 - (1 - probability ^ length) ^ paths)
    (weight : Outcome → ℝ) (normalized : ∑ outcome, weight outcome = 1) :
    (∑ sample, actualLongWeight blocks paths length probability weight sample) = 1 :=
  product_weight_normalized _ _ (product_weight_normalized weight weight normalized normalized)
    (sum_productWeight _ (actualBlockJointWeight_normalized20261012 paths length probability crossingPositive weight normalized))

theorem finiteMean_independent_sum20261012 {Sample : Type*} [Fintype Sample] [Nonempty Sample]
    (weight response : Sample → ℝ) (normalized : ∑ sample, weight sample = 1) (count : ℕ) :
    finiteMean (productWeight (Edge := Fin count) weight) (fun input => ∑ coordinate, response (input coordinate)) =
      (count : ℝ) * finiteMean weight response := by
  rw [finiteMean_sum20261012]
  simp only [finiteMean_coordinate20261012 weight normalized, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]

theorem actualLong_mean20261012 {Outcome : Type*} [Fintype Outcome] [Nonempty Outcome]
    (blocks paths length : ℕ) (probability : ℝ) (crossingPositive : 0 < 1 - (1 - probability ^ length) ^ paths)
    (weight response : Outcome → ℝ) (normalized : ∑ outcome, weight outcome = 1)
    (meanOne : finiteMean weight response = 1) :
    finiteMean (actualLongWeight blocks paths length probability weight) (actualLongResponse blocks paths length response) =
      2 + (blocks : ℝ) * actualBlockObservable paths length probability weight response id := by
  have blockNormalized := actualBlockJointWeight_normalized20261012 paths length probability crossingPositive weight normalized
  change finiteMean (fun sample : (Outcome × Outcome) × (Fin blocks → BlockSample paths length Outcome) =>
    (weight sample.1.1 * weight sample.1.2) * productWeight (actualBlockJointWeight paths length probability weight) sample.2)
    (fun sample => (response sample.1.1 + response sample.1.2) + ∑ block, actualBlockSampleResponse paths length response (sample.2 block)) = _
  rw [finiteMean_product (fun sample : Outcome × Outcome => weight sample.1 * weight sample.2)
    (productWeight (actualBlockJointWeight paths length probability weight))
    (fun exterior input => (response exterior.1 + response exterior.2) + ∑ block, actualBlockSampleResponse paths length response (input block))]
  have blockMean : finiteMean (actualBlockJointWeight paths length probability weight)
      (actualBlockSampleResponse paths length response) = actualBlockObservable paths length probability weight response id := by
    simpa only [id_eq] using actualBlockSample_observable20261012 paths length probability weight response id
  have inside (exterior : Outcome × Outcome) :
      finiteMean (productWeight (actualBlockJointWeight paths length probability weight))
        (fun input : Fin blocks → BlockSample paths length Outcome => (response exterior.1 + response exterior.2) + ∑ block, actualBlockSampleResponse paths length response (input block)) =
        response exterior.1 + response exterior.2 + (blocks : ℝ) * actualBlockObservable paths length probability weight response id := by
    rw [finiteMean_add, finiteMean_const _ (sum_productWeight _ blockNormalized),
      finiteMean_independent_sum20261012 _ _ blockNormalized blocks, blockMean]
  simp only [inside]
  rw [finiteMean_add, finiteMean_const _ (product_weight_normalized weight weight normalized normalized)]
  have exteriorMean : finiteMean (fun sample : Outcome × Outcome => weight sample.1 * weight sample.2)
      (fun sample => response sample.1 + response sample.2) = 2 := by
    rw [finiteMean_product weight weight (fun first second => response first + response second)]
    simp only [finiteMean_add, finiteMean_const weight normalized, meanOne]
    norm_num
  rw [exteriorMean]

theorem actualLong_variance_bound20261012 {Outcome : Type*} [Fintype Outcome] [Nonempty Outcome]
    (blocks paths length : ℕ) (probability : ℝ) (probabilityNonnegative : 0 ≤ probability)
    (probabilityAtMostOne : probability ≤ 1) (crossingPositive : 0 < 1 - (1 - probability ^ length) ^ paths)
    (weight response : Outcome → ℝ) (weightNonnegative : ∀ outcome, 0 ≤ weight outcome)
    (normalized : ∑ outcome, weight outcome = 1) (positive : ∀ outcome, 0 < response outcome)
    (lengthPositive : 0 < length) (meanOne : finiteMean weight response = 1)
    (varianceBound : finiteVariance weight response ≤ 8) :
    finiteVariance (actualLongWeight blocks paths length probability weight) (actualLongResponse blocks paths length response) ≤
      16 + (blocks : ℝ) * ((length : ℝ) ^ 2 + 8 * length) := by
  have blockNormalized := actualBlockJointWeight_normalized20261012 paths length probability crossingPositive weight normalized
  have blockSecond := actualBlock_second_moment20261012 paths length probability probabilityNonnegative probabilityAtMostOne
    crossingPositive weight response weightNonnegative normalized positive lengthPositive meanOne varianceBound
  rw [← actualBlockSample_observable20261012 paths length probability weight response (fun value => value ^ 2)] at blockSecond
  change finiteVariance (fun sample : (Outcome × Outcome) × (Fin blocks → BlockSample paths length Outcome) =>
    (weight sample.1.1 * weight sample.1.2) * productWeight (actualBlockJointWeight paths length probability weight) sample.2)
    (fun sample => (response sample.1.1 + response sample.1.2) + ∑ block, actualBlockSampleResponse paths length response (sample.2 block)) ≤ _
  rw [finiteVariance_product_add20261012 (fun sample : Outcome × Outcome => weight sample.1 * weight sample.2)
    (fun sample => response sample.1 + response sample.2)
    (productWeight (actualBlockJointWeight paths length probability weight))
    (fun input => ∑ block, actualBlockSampleResponse paths length response (input block))
    (product_weight_normalized weight weight normalized normalized)
    (sum_productWeight _ blockNormalized), finiteVariance_product_add20261012 weight response weight response normalized normalized]
  have sumBound := finiteVariance_independent_sum_le_second_moment20261012 _ _ blockNormalized blocks _ blockSecond
  linarith

end
end IGSIII4.SpectralDensity.ActualFamily
