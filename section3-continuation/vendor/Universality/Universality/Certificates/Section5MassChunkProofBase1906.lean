import Universality.Certificates.Section5MassChunkDataBase1906

namespace Universality.Certificates.MassChunksBase19

set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option exponentiation.threshold 10000
set_option Elab.async false

theorem transition0384_0400 :
    runLexMassChunk 2562 16 checkpoint0384 = checkpoint0400 := by
  decide +kernel

theorem values0384_0400 :
    checkpoint0384.value 2562 = checkpoint0400.value 2562 :=
  runLexMassChunk_value_of_check 2562 16
    checkpoint0384 checkpoint0400 transition0384_0400

#print axioms transition0384_0400
theorem transition0400_0416 :
    runLexMassChunk 2562 16 checkpoint0400 = checkpoint0416 := by
  decide +kernel

theorem values0400_0416 :
    checkpoint0400.value 2562 = checkpoint0416.value 2562 :=
  runLexMassChunk_value_of_check 2562 16
    checkpoint0400 checkpoint0416 transition0400_0416

#print axioms transition0400_0416
theorem transition0416_0424 :
    runLexMassChunk 2562 8 checkpoint0416 = checkpoint0424 := by
  decide +kernel

theorem values0416_0424 :
    checkpoint0416.value 2562 = checkpoint0424.value 2562 :=
  runLexMassChunk_value_of_check 2562 8
    checkpoint0416 checkpoint0424 transition0416_0424

#print axioms transition0416_0424

end Universality.Certificates.MassChunksBase19
