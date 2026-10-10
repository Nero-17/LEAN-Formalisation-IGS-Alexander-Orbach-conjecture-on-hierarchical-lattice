import Universality.Certificates.Section5MassChunkDataShifted1901
import Universality.Certificates.Section5MassChunkDataShifted1900

namespace Universality.Certificates.MassChunksShifted19

set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option exponentiation.threshold 10000
set_option Elab.async false

theorem transition0064_0080 :
    runLexMassChunk 2562 16 checkpoint0064 = checkpoint0080 := by
  decide +kernel

theorem values0064_0080 :
    checkpoint0064.value 2562 = checkpoint0080.value 2562 :=
  runLexMassChunk_value_of_check 2562 16
    checkpoint0064 checkpoint0080 transition0064_0080

#print axioms transition0064_0080
theorem transition0080_0096 :
    runLexMassChunk 2562 16 checkpoint0080 = checkpoint0096 := by
  decide +kernel

theorem values0080_0096 :
    checkpoint0080.value 2562 = checkpoint0096.value 2562 :=
  runLexMassChunk_value_of_check 2562 16
    checkpoint0080 checkpoint0096 transition0080_0096

#print axioms transition0080_0096
theorem transition0096_0112 :
    runLexMassChunk 2562 16 checkpoint0096 = checkpoint0112 := by
  decide +kernel

theorem values0096_0112 :
    checkpoint0096.value 2562 = checkpoint0112.value 2562 :=
  runLexMassChunk_value_of_check 2562 16
    checkpoint0096 checkpoint0112 transition0096_0112

#print axioms transition0096_0112
theorem transition0112_0128 :
    runLexMassChunk 2562 16 checkpoint0112 = checkpoint0128 := by
  decide +kernel

theorem values0112_0128 :
    checkpoint0112.value 2562 = checkpoint0128.value 2562 :=
  runLexMassChunk_value_of_check 2562 16
    checkpoint0112 checkpoint0128 transition0112_0128

#print axioms transition0112_0128

end Universality.Certificates.MassChunksShifted19
