import Universality.Certificates.Section5MassChunkDataBase73908
import Universality.Certificates.Section5MassChunkDataBase73907

namespace Universality.Certificates.MassChunksBase739

set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option exponentiation.threshold 10000
set_option Elab.async false

theorem transition0512_0528 :
    runLexMassChunk 5730 16 checkpoint0512 = checkpoint0528 := by
  decide +kernel

theorem values0512_0528 :
    checkpoint0512.value 5730 = checkpoint0528.value 5730 :=
  runLexMassChunk_value_of_check 5730 16
    checkpoint0512 checkpoint0528 transition0512_0528

#print axioms transition0512_0528
theorem transition0528_0544 :
    runLexMassChunk 5730 16 checkpoint0528 = checkpoint0544 := by
  decide +kernel

theorem values0528_0544 :
    checkpoint0528.value 5730 = checkpoint0544.value 5730 :=
  runLexMassChunk_value_of_check 5730 16
    checkpoint0528 checkpoint0544 transition0528_0544

#print axioms transition0528_0544
theorem transition0544_0560 :
    runLexMassChunk 5730 16 checkpoint0544 = checkpoint0560 := by
  decide +kernel

theorem values0544_0560 :
    checkpoint0544.value 5730 = checkpoint0560.value 5730 :=
  runLexMassChunk_value_of_check 5730 16
    checkpoint0544 checkpoint0560 transition0544_0560

#print axioms transition0544_0560
theorem transition0560_0576 :
    runLexMassChunk 5730 16 checkpoint0560 = checkpoint0576 := by
  decide +kernel

theorem values0560_0576 :
    checkpoint0560.value 5730 = checkpoint0576.value 5730 :=
  runLexMassChunk_value_of_check 5730 16
    checkpoint0560 checkpoint0576 transition0560_0576

#print axioms transition0560_0576

end Universality.Certificates.MassChunksBase739
