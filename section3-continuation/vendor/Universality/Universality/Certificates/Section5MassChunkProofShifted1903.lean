import Universality.Certificates.Section5MassChunkDataShifted1903
import Universality.Certificates.Section5MassChunkDataShifted1902

namespace Universality.Certificates.MassChunksShifted19

set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option exponentiation.threshold 10000
set_option Elab.async false

theorem transition0192_0208 :
    runLexMassChunk 2562 16 checkpoint0192 = checkpoint0208 := by
  decide +kernel

theorem values0192_0208 :
    checkpoint0192.value 2562 = checkpoint0208.value 2562 :=
  runLexMassChunk_value_of_check 2562 16
    checkpoint0192 checkpoint0208 transition0192_0208

#print axioms transition0192_0208
theorem transition0208_0224 :
    runLexMassChunk 2562 16 checkpoint0208 = checkpoint0224 := by
  decide +kernel

theorem values0208_0224 :
    checkpoint0208.value 2562 = checkpoint0224.value 2562 :=
  runLexMassChunk_value_of_check 2562 16
    checkpoint0208 checkpoint0224 transition0208_0224

#print axioms transition0208_0224
theorem transition0224_0240 :
    runLexMassChunk 2562 16 checkpoint0224 = checkpoint0240 := by
  decide +kernel

theorem values0224_0240 :
    checkpoint0224.value 2562 = checkpoint0240.value 2562 :=
  runLexMassChunk_value_of_check 2562 16
    checkpoint0224 checkpoint0240 transition0224_0240

#print axioms transition0224_0240
theorem transition0240_0256 :
    runLexMassChunk 2562 16 checkpoint0240 = checkpoint0256 := by
  decide +kernel

theorem values0240_0256 :
    checkpoint0240.value 2562 = checkpoint0256.value 2562 :=
  runLexMassChunk_value_of_check 2562 16
    checkpoint0240 checkpoint0256 transition0240_0256

#print axioms transition0240_0256

end Universality.Certificates.MassChunksShifted19
