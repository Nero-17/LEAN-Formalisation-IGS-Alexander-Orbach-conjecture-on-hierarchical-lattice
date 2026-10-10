import Universality.Certificates.Section5MassChunkDataShifted1902
import Universality.Certificates.Section5MassChunkDataShifted1901

namespace Universality.Certificates.MassChunksShifted19

set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option exponentiation.threshold 10000
set_option Elab.async false

theorem transition0128_0144 :
    runLexMassChunk 2562 16 checkpoint0128 = checkpoint0144 := by
  decide +kernel

theorem values0128_0144 :
    checkpoint0128.value 2562 = checkpoint0144.value 2562 :=
  runLexMassChunk_value_of_check 2562 16
    checkpoint0128 checkpoint0144 transition0128_0144

#print axioms transition0128_0144
theorem transition0144_0160 :
    runLexMassChunk 2562 16 checkpoint0144 = checkpoint0160 := by
  decide +kernel

theorem values0144_0160 :
    checkpoint0144.value 2562 = checkpoint0160.value 2562 :=
  runLexMassChunk_value_of_check 2562 16
    checkpoint0144 checkpoint0160 transition0144_0160

#print axioms transition0144_0160
theorem transition0160_0176 :
    runLexMassChunk 2562 16 checkpoint0160 = checkpoint0176 := by
  decide +kernel

theorem values0160_0176 :
    checkpoint0160.value 2562 = checkpoint0176.value 2562 :=
  runLexMassChunk_value_of_check 2562 16
    checkpoint0160 checkpoint0176 transition0160_0176

#print axioms transition0160_0176
theorem transition0176_0192 :
    runLexMassChunk 2562 16 checkpoint0176 = checkpoint0192 := by
  decide +kernel

theorem values0176_0192 :
    checkpoint0176.value 2562 = checkpoint0192.value 2562 :=
  runLexMassChunk_value_of_check 2562 16
    checkpoint0176 checkpoint0192 transition0176_0192

#print axioms transition0176_0192

end Universality.Certificates.MassChunksShifted19
