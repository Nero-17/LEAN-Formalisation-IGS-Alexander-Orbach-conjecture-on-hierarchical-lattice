import Universality.Certificates.Section5MassChunkDataBase66100

namespace Universality.Certificates.MassChunksBase661

set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option exponentiation.threshold 10000
set_option Elab.async false

theorem transition0000_0016 :
    runLexMassChunk 5634 16 checkpoint0000 = checkpoint0016 := by
  decide +kernel

theorem values0000_0016 :
    checkpoint0000.value 5634 = checkpoint0016.value 5634 :=
  runLexMassChunk_value_of_check 5634 16
    checkpoint0000 checkpoint0016 transition0000_0016

#print axioms transition0000_0016
theorem transition0016_0032 :
    runLexMassChunk 5634 16 checkpoint0016 = checkpoint0032 := by
  decide +kernel

theorem values0016_0032 :
    checkpoint0016.value 5634 = checkpoint0032.value 5634 :=
  runLexMassChunk_value_of_check 5634 16
    checkpoint0016 checkpoint0032 transition0016_0032

#print axioms transition0016_0032
theorem transition0032_0048 :
    runLexMassChunk 5634 16 checkpoint0032 = checkpoint0048 := by
  decide +kernel

theorem values0032_0048 :
    checkpoint0032.value 5634 = checkpoint0048.value 5634 :=
  runLexMassChunk_value_of_check 5634 16
    checkpoint0032 checkpoint0048 transition0032_0048

#print axioms transition0032_0048
theorem transition0048_0064 :
    runLexMassChunk 5634 16 checkpoint0048 = checkpoint0064 := by
  decide +kernel

theorem values0048_0064 :
    checkpoint0048.value 5634 = checkpoint0064.value 5634 :=
  runLexMassChunk_value_of_check 5634 16
    checkpoint0048 checkpoint0064 transition0048_0064

#print axioms transition0048_0064

end Universality.Certificates.MassChunksBase661
