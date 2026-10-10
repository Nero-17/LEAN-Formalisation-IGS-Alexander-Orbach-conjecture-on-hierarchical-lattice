import Universality.Certificates.Section5MassChunkDataBase66106
import Universality.Certificates.Section5MassChunkDataBase66105

namespace Universality.Certificates.MassChunksBase661

set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option exponentiation.threshold 10000
set_option Elab.async false

theorem transition0384_0400 :
    runLexMassChunk 5634 16 checkpoint0384 = checkpoint0400 := by
  decide +kernel

theorem values0384_0400 :
    checkpoint0384.value 5634 = checkpoint0400.value 5634 :=
  runLexMassChunk_value_of_check 5634 16
    checkpoint0384 checkpoint0400 transition0384_0400

#print axioms transition0384_0400
theorem transition0400_0416 :
    runLexMassChunk 5634 16 checkpoint0400 = checkpoint0416 := by
  decide +kernel

theorem values0400_0416 :
    checkpoint0400.value 5634 = checkpoint0416.value 5634 :=
  runLexMassChunk_value_of_check 5634 16
    checkpoint0400 checkpoint0416 transition0400_0416

#print axioms transition0400_0416
theorem transition0416_0432 :
    runLexMassChunk 5634 16 checkpoint0416 = checkpoint0432 := by
  decide +kernel

theorem values0416_0432 :
    checkpoint0416.value 5634 = checkpoint0432.value 5634 :=
  runLexMassChunk_value_of_check 5634 16
    checkpoint0416 checkpoint0432 transition0416_0432

#print axioms transition0416_0432
theorem transition0432_0448 :
    runLexMassChunk 5634 16 checkpoint0432 = checkpoint0448 := by
  decide +kernel

theorem values0432_0448 :
    checkpoint0432.value 5634 = checkpoint0448.value 5634 :=
  runLexMassChunk_value_of_check 5634 16
    checkpoint0432 checkpoint0448 transition0432_0448

#print axioms transition0432_0448

end Universality.Certificates.MassChunksBase661
