import Universality.Certificates.Opposite.Batch00
import Universality.Certificates.Opposite.Batch01
import Universality.Certificates.Opposite.Batch02
import Universality.Certificates.Opposite.Batch03
import Universality.Certificates.Opposite.Batch04
import Universality.Certificates.Opposite.Batch05
import Universality.Certificates.Opposite.Batch06
import Universality.Certificates.Opposite.Batch07
import Universality.Certificates.Opposite.Batch08
import Universality.Certificates.Opposite.Batch09
import Universality.Certificates.Opposite.Batch10
import Universality.Certificates.Opposite.Batch11
import Universality.Certificates.Opposite.Batch12
import Universality.Certificates.Opposite.Batch13
import Universality.Certificates.Opposite.Batch14
import Universality.Certificates.Opposite.Batch15
import Universality.Certificates.Opposite.Batch16
import Universality.Certificates.Opposite.Batch17
import Universality.Certificates.Opposite.Batch18
import Universality.Certificates.Opposite.Batch19
import Universality.Certificates.Opposite.Batch20
import Universality.Certificates.Opposite.Batch21
import Universality.Certificates.Opposite.Batch22
import Universality.Certificates.Opposite.Batch23
import Universality.Certificates.Opposite.Batch24
import Universality.Certificates.Opposite.Batch25
import Universality.Certificates.Opposite.Batch26
import Universality.Certificates.Opposite.Batch27
import Universality.Certificates.Opposite.Batch28
import Universality.Certificates.Opposite.Batch29
import Universality.Certificates.Opposite.Batch30
import Universality.Certificates.Opposite.Batch31
import Universality.Certificates.Opposite.Batch32
import Universality.Certificates.Opposite.Batch33
import Universality.Certificates.Opposite.Batch34
import Universality.Certificates.Opposite.Batch35
import Universality.Certificates.Opposite.Batch36
import Universality.Certificates.Opposite.Batch37
import Universality.Certificates.Opposite.Batch38
import Universality.Certificates.Opposite.Batch39
import Universality.Certificates.Opposite.Batch40
import Universality.Certificates.Opposite.Batch41
import Universality.Certificates.Opposite.Batch42
import Universality.Certificates.Opposite.Batch43
import Universality.Certificates.Opposite.Batch44
import Universality.Certificates.Opposite.Batch45
import Universality.Certificates.Opposite.Batch46
import Universality.Certificates.Opposite.Batch47
import Universality.Certificates.Opposite.Batch48
import Universality.Certificates.Opposite.Batch49
import Universality.Certificates.Opposite.Batch50
import Universality.Certificates.Opposite.Batch51
import Universality.Certificates.Opposite.Batch52
import Universality.Certificates.Opposite.Batch53
import Universality.Certificates.Opposite.Batch54
import Universality.Certificates.Opposite.Batch55
import Universality.Certificates.Opposite.Batch56
import Universality.Certificates.Opposite.Batch57
import Universality.Certificates.Opposite.Batch58
import Universality.Certificates.Opposite.Batch59
import Universality.Certificates.Opposite.Batch60
import Universality.Certificates.Opposite.Batch61
import Universality.Certificates.Opposite.Batch62
import Universality.Certificates.Opposite.Batch63

namespace Universality
open FiniteNetwork

def oppositeComponentRows : List (ComponentRow 8 13) :=
  oppositeRows00 ++
  oppositeRows01 ++
  oppositeRows02 ++
  oppositeRows03 ++
  oppositeRows04 ++
  oppositeRows05 ++
  oppositeRows06 ++
  oppositeRows07 ++
  oppositeRows08 ++
  oppositeRows09 ++
  oppositeRows10 ++
  oppositeRows11 ++
  oppositeRows12 ++
  oppositeRows13 ++
  oppositeRows14 ++
  oppositeRows15 ++
  oppositeRows16 ++
  oppositeRows17 ++
  oppositeRows18 ++
  oppositeRows19 ++
  oppositeRows20 ++
  oppositeRows21 ++
  oppositeRows22 ++
  oppositeRows23 ++
  oppositeRows24 ++
  oppositeRows25 ++
  oppositeRows26 ++
  oppositeRows27 ++
  oppositeRows28 ++
  oppositeRows29 ++
  oppositeRows30 ++
  oppositeRows31 ++
  oppositeRows32 ++
  oppositeRows33 ++
  oppositeRows34 ++
  oppositeRows35 ++
  oppositeRows36 ++
  oppositeRows37 ++
  oppositeRows38 ++
  oppositeRows39 ++
  oppositeRows40 ++
  oppositeRows41 ++
  oppositeRows42 ++
  oppositeRows43 ++
  oppositeRows44 ++
  oppositeRows45 ++
  oppositeRows46 ++
  oppositeRows47 ++
  oppositeRows48 ++
  oppositeRows49 ++
  oppositeRows50 ++
  oppositeRows51 ++
  oppositeRows52 ++
  oppositeRows53 ++
  oppositeRows54 ++
  oppositeRows55 ++
  oppositeRows56 ++
  oppositeRows57 ++
  oppositeRows58 ++
  oppositeRows59 ++
  oppositeRows60 ++
  oppositeRows61 ++
  oppositeRows62 ++
  oppositeRows63

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem oppositeComponentRows_indices :
    oppositeComponentRows.map ComponentRow.index = List.finRange (2 ^ 13) := by
  decide

theorem oppositeComponentRows_valid :
    ∀ row ∈ oppositeComponentRows, row.Valid oppositeWheatstoneNetwork := by
  have h : oppositeComponentRows.all (fun row => decide (row.Valid oppositeWheatstoneNetwork)) = true := by
    simp only [oppositeComponentRows, List.all_append,
    oppositeRows00_valid,
    oppositeRows01_valid,
    oppositeRows02_valid,
    oppositeRows03_valid,
    oppositeRows04_valid,
    oppositeRows05_valid,
    oppositeRows06_valid,
    oppositeRows07_valid,
    oppositeRows08_valid,
    oppositeRows09_valid,
    oppositeRows10_valid,
    oppositeRows11_valid,
    oppositeRows12_valid,
    oppositeRows13_valid,
    oppositeRows14_valid,
    oppositeRows15_valid,
    oppositeRows16_valid,
    oppositeRows17_valid,
    oppositeRows18_valid,
    oppositeRows19_valid,
    oppositeRows20_valid,
    oppositeRows21_valid,
    oppositeRows22_valid,
    oppositeRows23_valid,
    oppositeRows24_valid,
    oppositeRows25_valid,
    oppositeRows26_valid,
    oppositeRows27_valid,
    oppositeRows28_valid,
    oppositeRows29_valid,
    oppositeRows30_valid,
    oppositeRows31_valid,
    oppositeRows32_valid,
    oppositeRows33_valid,
    oppositeRows34_valid,
    oppositeRows35_valid,
    oppositeRows36_valid,
    oppositeRows37_valid,
    oppositeRows38_valid,
    oppositeRows39_valid,
    oppositeRows40_valid,
    oppositeRows41_valid,
    oppositeRows42_valid,
    oppositeRows43_valid,
    oppositeRows44_valid,
    oppositeRows45_valid,
    oppositeRows46_valid,
    oppositeRows47_valid,
    oppositeRows48_valid,
    oppositeRows49_valid,
    oppositeRows50_valid,
    oppositeRows51_valid,
    oppositeRows52_valid,
    oppositeRows53_valid,
    oppositeRows54_valid,
    oppositeRows55_valid,
    oppositeRows56_valid,
    oppositeRows57_valid,
    oppositeRows58_valid,
    oppositeRows59_valid,
    oppositeRows60_valid,
    oppositeRows61_valid,
    oppositeRows62_valid,
    oppositeRows63_valid]
    rfl
  simpa only [List.all_eq_true, decide_eq_true_eq] using h

def oppositeWheatstoneCountTable : LiveState → LiveState → ℕ
  | .connected, .connected => 30336
  | .connected, .both => 14912
  | .connected, .single => 6848
  | .both, .connected => 20064
  | .both, .both => 15520
  | .both, .single => 13120
  | .single, .connected => 10032
  | .single, .both => 3472
  | .single, .single => 15136

set_option maxHeartbeats 2000000 in
theorem oppositeWheatstone_exact_counts :
    (∀ σ, oppositeWheatstoneNetwork.conditioningCount σ = 4096) ∧
    (∀ σ τ, oppositeWheatstoneNetwork.conditionalCount σ τ = oppositeWheatstoneCountTable σ τ) := by
  constructor
  · intro σ
    rw [← certified_conditioningCount oppositeWheatstoneNetwork oppositeComponentRows
      oppositeComponentRows_indices oppositeComponentRows_valid]
    simp only [oppositeComponentRows, List.map_append, List.sum_append,
    oppositeRows00_counts.1,
    oppositeRows01_counts.1,
    oppositeRows02_counts.1,
    oppositeRows03_counts.1,
    oppositeRows04_counts.1,
    oppositeRows05_counts.1,
    oppositeRows06_counts.1,
    oppositeRows07_counts.1,
    oppositeRows08_counts.1,
    oppositeRows09_counts.1,
    oppositeRows10_counts.1,
    oppositeRows11_counts.1,
    oppositeRows12_counts.1,
    oppositeRows13_counts.1,
    oppositeRows14_counts.1,
    oppositeRows15_counts.1,
    oppositeRows16_counts.1,
    oppositeRows17_counts.1,
    oppositeRows18_counts.1,
    oppositeRows19_counts.1,
    oppositeRows20_counts.1,
    oppositeRows21_counts.1,
    oppositeRows22_counts.1,
    oppositeRows23_counts.1,
    oppositeRows24_counts.1,
    oppositeRows25_counts.1,
    oppositeRows26_counts.1,
    oppositeRows27_counts.1,
    oppositeRows28_counts.1,
    oppositeRows29_counts.1,
    oppositeRows30_counts.1,
    oppositeRows31_counts.1,
    oppositeRows32_counts.1,
    oppositeRows33_counts.1,
    oppositeRows34_counts.1,
    oppositeRows35_counts.1,
    oppositeRows36_counts.1,
    oppositeRows37_counts.1,
    oppositeRows38_counts.1,
    oppositeRows39_counts.1,
    oppositeRows40_counts.1,
    oppositeRows41_counts.1,
    oppositeRows42_counts.1,
    oppositeRows43_counts.1,
    oppositeRows44_counts.1,
    oppositeRows45_counts.1,
    oppositeRows46_counts.1,
    oppositeRows47_counts.1,
    oppositeRows48_counts.1,
    oppositeRows49_counts.1,
    oppositeRows50_counts.1,
    oppositeRows51_counts.1,
    oppositeRows52_counts.1,
    oppositeRows53_counts.1,
    oppositeRows54_counts.1,
    oppositeRows55_counts.1,
    oppositeRows56_counts.1,
    oppositeRows57_counts.1,
    oppositeRows58_counts.1,
    oppositeRows59_counts.1,
    oppositeRows60_counts.1,
    oppositeRows61_counts.1,
    oppositeRows62_counts.1,
    oppositeRows63_counts.1]
    cases σ <;> rfl
  · intro σ τ
    rw [← certified_conditionalCount oppositeWheatstoneNetwork oppositeComponentRows
      oppositeComponentRows_indices oppositeComponentRows_valid]
    simp only [oppositeComponentRows, List.map_append, List.sum_append,
    oppositeRows00_counts.2,
    oppositeRows01_counts.2,
    oppositeRows02_counts.2,
    oppositeRows03_counts.2,
    oppositeRows04_counts.2,
    oppositeRows05_counts.2,
    oppositeRows06_counts.2,
    oppositeRows07_counts.2,
    oppositeRows08_counts.2,
    oppositeRows09_counts.2,
    oppositeRows10_counts.2,
    oppositeRows11_counts.2,
    oppositeRows12_counts.2,
    oppositeRows13_counts.2,
    oppositeRows14_counts.2,
    oppositeRows15_counts.2,
    oppositeRows16_counts.2,
    oppositeRows17_counts.2,
    oppositeRows18_counts.2,
    oppositeRows19_counts.2,
    oppositeRows20_counts.2,
    oppositeRows21_counts.2,
    oppositeRows22_counts.2,
    oppositeRows23_counts.2,
    oppositeRows24_counts.2,
    oppositeRows25_counts.2,
    oppositeRows26_counts.2,
    oppositeRows27_counts.2,
    oppositeRows28_counts.2,
    oppositeRows29_counts.2,
    oppositeRows30_counts.2,
    oppositeRows31_counts.2,
    oppositeRows32_counts.2,
    oppositeRows33_counts.2,
    oppositeRows34_counts.2,
    oppositeRows35_counts.2,
    oppositeRows36_counts.2,
    oppositeRows37_counts.2,
    oppositeRows38_counts.2,
    oppositeRows39_counts.2,
    oppositeRows40_counts.2,
    oppositeRows41_counts.2,
    oppositeRows42_counts.2,
    oppositeRows43_counts.2,
    oppositeRows44_counts.2,
    oppositeRows45_counts.2,
    oppositeRows46_counts.2,
    oppositeRows47_counts.2,
    oppositeRows48_counts.2,
    oppositeRows49_counts.2,
    oppositeRows50_counts.2,
    oppositeRows51_counts.2,
    oppositeRows52_counts.2,
    oppositeRows53_counts.2,
    oppositeRows54_counts.2,
    oppositeRows55_counts.2,
    oppositeRows56_counts.2,
    oppositeRows57_counts.2,
    oppositeRows58_counts.2,
    oppositeRows59_counts.2,
    oppositeRows60_counts.2,
    oppositeRows61_counts.2,
    oppositeRows62_counts.2,
    oppositeRows63_counts.2]
    cases σ <;> cases τ <;> rfl

theorem oppositeWheatstone_fair_mass (σ τ : LiveState) :
    oppositeWheatstoneNetwork.fairMassMatrix σ τ = (oppositeWheatstoneCountTable σ τ : ℚ) / 4096 := by
  simp [fairMassMatrix, oppositeWheatstone_exact_counts.1, oppositeWheatstone_exact_counts.2]

theorem oppositeWheatstone_fair_block :
    fairMassBlock oppositeWheatstoneNetwork = oppositeWheatstoneBlock := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [fairMassBlock, oppositeWheatstone_fair_mass, oppositeWheatstoneCountTable,
      oppositeWheatstoneBlock]

end Universality
