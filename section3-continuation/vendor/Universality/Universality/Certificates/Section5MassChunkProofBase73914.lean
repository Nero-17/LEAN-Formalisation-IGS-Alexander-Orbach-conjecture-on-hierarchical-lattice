import Universality.Certificates.Section5MassChunkDataBase73914
import Universality.Certificates.Section5MassChunkDataBase73913

namespace Universality.Certificates.MassChunksBase739

set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option exponentiation.threshold 10000
set_option Elab.async false

theorem transition0896_0912 :
    runLexMassChunk 5730 16 checkpoint0896 = checkpoint0912 := by
  decide +kernel

theorem values0896_0912 :
    checkpoint0896.value 5730 = checkpoint0912.value 5730 :=
  runLexMassChunk_value_of_check 5730 16
    checkpoint0896 checkpoint0912 transition0896_0912

#print axioms transition0896_0912
theorem transition0912_0928 :
    runLexMassChunk 5730 16 checkpoint0912 = checkpoint0928 := by
  decide +kernel

theorem values0912_0928 :
    checkpoint0912.value 5730 = checkpoint0928.value 5730 :=
  runLexMassChunk_value_of_check 5730 16
    checkpoint0912 checkpoint0928 transition0912_0928

#print axioms transition0912_0928
theorem transition0928_0944 :
    runLexMassChunk 5730 16 checkpoint0928 = checkpoint0944 := by
  decide +kernel

theorem values0928_0944 :
    checkpoint0928.value 5730 = checkpoint0944.value 5730 :=
  runLexMassChunk_value_of_check 5730 16
    checkpoint0928 checkpoint0944 transition0928_0944

#print axioms transition0928_0944
theorem transition0944_0952 :
    runLexMassChunk 5730 8 checkpoint0944 = checkpoint0952 := by
  decide +kernel

theorem values0944_0952 :
    checkpoint0944.value 5730 = checkpoint0952.value 5730 :=
  runLexMassChunk_value_of_check 5730 8
    checkpoint0944 checkpoint0952 transition0944_0952

#print axioms transition0944_0952

end Universality.Certificates.MassChunksBase739
