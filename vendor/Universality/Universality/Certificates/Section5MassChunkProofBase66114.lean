import Universality.Certificates.Section5MassChunkDataBase66114
import Universality.Certificates.Section5MassChunkDataBase66113

namespace Universality.Certificates.MassChunksBase661

set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option exponentiation.threshold 10000
set_option Elab.async false

theorem transition0896_0912 :
    runLexMassChunk 5634 16 checkpoint0896 = checkpoint0912 := by
  decide +kernel

theorem values0896_0912 :
    checkpoint0896.value 5634 = checkpoint0912.value 5634 :=
  runLexMassChunk_value_of_check 5634 16
    checkpoint0896 checkpoint0912 transition0896_0912

#print axioms transition0896_0912
theorem transition0912_0928 :
    runLexMassChunk 5634 16 checkpoint0912 = checkpoint0928 := by
  decide +kernel

theorem values0912_0928 :
    checkpoint0912.value 5634 = checkpoint0928.value 5634 :=
  runLexMassChunk_value_of_check 5634 16
    checkpoint0912 checkpoint0928 transition0912_0928

#print axioms transition0912_0928
theorem transition0928_0936 :
    runLexMassChunk 5634 8 checkpoint0928 = checkpoint0936 := by
  decide +kernel

theorem values0928_0936 :
    checkpoint0928.value 5634 = checkpoint0936.value 5634 :=
  runLexMassChunk_value_of_check 5634 8
    checkpoint0928 checkpoint0936 transition0928_0936

#print axioms transition0928_0936

end Universality.Certificates.MassChunksBase661
