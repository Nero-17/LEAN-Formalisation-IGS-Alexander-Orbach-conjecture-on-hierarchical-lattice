import Universality.Certificates.Section5MassChunkDataBase66113
import Universality.Certificates.Section5MassChunkDataBase66112

namespace Universality.Certificates.MassChunksBase661

set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option exponentiation.threshold 10000
set_option Elab.async false

theorem transition0832_0848 :
    runLexMassChunk 5634 16 checkpoint0832 = checkpoint0848 := by
  decide +kernel

theorem values0832_0848 :
    checkpoint0832.value 5634 = checkpoint0848.value 5634 :=
  runLexMassChunk_value_of_check 5634 16
    checkpoint0832 checkpoint0848 transition0832_0848

#print axioms transition0832_0848
theorem transition0848_0864 :
    runLexMassChunk 5634 16 checkpoint0848 = checkpoint0864 := by
  decide +kernel

theorem values0848_0864 :
    checkpoint0848.value 5634 = checkpoint0864.value 5634 :=
  runLexMassChunk_value_of_check 5634 16
    checkpoint0848 checkpoint0864 transition0848_0864

#print axioms transition0848_0864
theorem transition0864_0880 :
    runLexMassChunk 5634 16 checkpoint0864 = checkpoint0880 := by
  decide +kernel

theorem values0864_0880 :
    checkpoint0864.value 5634 = checkpoint0880.value 5634 :=
  runLexMassChunk_value_of_check 5634 16
    checkpoint0864 checkpoint0880 transition0864_0880

#print axioms transition0864_0880
theorem transition0880_0896 :
    runLexMassChunk 5634 16 checkpoint0880 = checkpoint0896 := by
  decide +kernel

theorem values0880_0896 :
    checkpoint0880.value 5634 = checkpoint0896.value 5634 :=
  runLexMassChunk_value_of_check 5634 16
    checkpoint0880 checkpoint0896 transition0880_0896

#print axioms transition0880_0896

end Universality.Certificates.MassChunksBase661
