import Universality.Certificates.Section5MassChunkDataBase1905

namespace Universality.Certificates.MassChunksBase19

set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option exponentiation.threshold 10000
set_option Elab.async false

theorem transition0320_0336 :
    runLexMassChunk 2562 16 checkpoint0320 = checkpoint0336 := by
  decide +kernel

theorem values0320_0336 :
    checkpoint0320.value 2562 = checkpoint0336.value 2562 :=
  runLexMassChunk_value_of_check 2562 16
    checkpoint0320 checkpoint0336 transition0320_0336

#print axioms transition0320_0336
theorem transition0336_0352 :
    runLexMassChunk 2562 16 checkpoint0336 = checkpoint0352 := by
  decide +kernel

theorem values0336_0352 :
    checkpoint0336.value 2562 = checkpoint0352.value 2562 :=
  runLexMassChunk_value_of_check 2562 16
    checkpoint0336 checkpoint0352 transition0336_0352

#print axioms transition0336_0352
theorem transition0352_0368 :
    runLexMassChunk 2562 16 checkpoint0352 = checkpoint0368 := by
  decide +kernel

theorem values0352_0368 :
    checkpoint0352.value 2562 = checkpoint0368.value 2562 :=
  runLexMassChunk_value_of_check 2562 16
    checkpoint0352 checkpoint0368 transition0352_0368

#print axioms transition0352_0368
theorem transition0368_0384 :
    runLexMassChunk 2562 16 checkpoint0368 = checkpoint0384 := by
  decide +kernel

theorem values0368_0384 :
    checkpoint0368.value 2562 = checkpoint0384.value 2562 :=
  runLexMassChunk_value_of_check 2562 16
    checkpoint0368 checkpoint0384 transition0368_0384

#print axioms transition0368_0384

end Universality.Certificates.MassChunksBase19
