import Universality.Certificates.Section5MassChunkDataBase1904

namespace Universality.Certificates.MassChunksBase19

set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option exponentiation.threshold 10000
set_option Elab.async false

theorem transition0256_0272 :
    runLexMassChunk 2562 16 checkpoint0256 = checkpoint0272 := by
  decide +kernel

theorem values0256_0272 :
    checkpoint0256.value 2562 = checkpoint0272.value 2562 :=
  runLexMassChunk_value_of_check 2562 16
    checkpoint0256 checkpoint0272 transition0256_0272

#print axioms transition0256_0272
theorem transition0272_0288 :
    runLexMassChunk 2562 16 checkpoint0272 = checkpoint0288 := by
  decide +kernel

theorem values0272_0288 :
    checkpoint0272.value 2562 = checkpoint0288.value 2562 :=
  runLexMassChunk_value_of_check 2562 16
    checkpoint0272 checkpoint0288 transition0272_0288

#print axioms transition0272_0288
theorem transition0288_0304 :
    runLexMassChunk 2562 16 checkpoint0288 = checkpoint0304 := by
  decide +kernel

theorem values0288_0304 :
    checkpoint0288.value 2562 = checkpoint0304.value 2562 :=
  runLexMassChunk_value_of_check 2562 16
    checkpoint0288 checkpoint0304 transition0288_0304

#print axioms transition0288_0304
theorem transition0304_0320 :
    runLexMassChunk 2562 16 checkpoint0304 = checkpoint0320 := by
  decide +kernel

theorem values0304_0320 :
    checkpoint0304.value 2562 = checkpoint0320.value 2562 :=
  runLexMassChunk_value_of_check 2562 16
    checkpoint0304 checkpoint0320 transition0304_0320

#print axioms transition0304_0320

end Universality.Certificates.MassChunksBase19
