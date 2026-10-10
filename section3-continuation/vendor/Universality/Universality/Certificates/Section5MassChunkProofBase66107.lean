import Universality.Certificates.Section5MassChunkDataBase66107
import Universality.Certificates.Section5MassChunkDataBase66106

namespace Universality.Certificates.MassChunksBase661

set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option exponentiation.threshold 10000
set_option Elab.async false

theorem transition0448_0464 :
    runLexMassChunk 5634 16 checkpoint0448 = checkpoint0464 := by
  decide +kernel

theorem values0448_0464 :
    checkpoint0448.value 5634 = checkpoint0464.value 5634 :=
  runLexMassChunk_value_of_check 5634 16
    checkpoint0448 checkpoint0464 transition0448_0464

#print axioms transition0448_0464
theorem transition0464_0480 :
    runLexMassChunk 5634 16 checkpoint0464 = checkpoint0480 := by
  decide +kernel

theorem values0464_0480 :
    checkpoint0464.value 5634 = checkpoint0480.value 5634 :=
  runLexMassChunk_value_of_check 5634 16
    checkpoint0464 checkpoint0480 transition0464_0480

#print axioms transition0464_0480
theorem transition0480_0496 :
    runLexMassChunk 5634 16 checkpoint0480 = checkpoint0496 := by
  decide +kernel

theorem values0480_0496 :
    checkpoint0480.value 5634 = checkpoint0496.value 5634 :=
  runLexMassChunk_value_of_check 5634 16
    checkpoint0480 checkpoint0496 transition0480_0496

#print axioms transition0480_0496
theorem transition0496_0512 :
    runLexMassChunk 5634 16 checkpoint0496 = checkpoint0512 := by
  decide +kernel

theorem values0496_0512 :
    checkpoint0496.value 5634 = checkpoint0512.value 5634 :=
  runLexMassChunk_value_of_check 5634 16
    checkpoint0496 checkpoint0512 transition0496_0512

#print axioms transition0496_0512

end Universality.Certificates.MassChunksBase661
