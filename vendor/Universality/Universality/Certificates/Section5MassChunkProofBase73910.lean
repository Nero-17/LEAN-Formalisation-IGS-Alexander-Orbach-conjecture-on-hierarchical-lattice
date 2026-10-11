import Universality.Certificates.Section5MassChunkDataBase73910
import Universality.Certificates.Section5MassChunkDataBase73909

namespace Universality.Certificates.MassChunksBase739

set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option exponentiation.threshold 10000
set_option Elab.async false

theorem transition0640_0656 :
    runLexMassChunk 5730 16 checkpoint0640 = checkpoint0656 := by
  decide +kernel

theorem values0640_0656 :
    checkpoint0640.value 5730 = checkpoint0656.value 5730 :=
  runLexMassChunk_value_of_check 5730 16
    checkpoint0640 checkpoint0656 transition0640_0656

#print axioms transition0640_0656
theorem transition0656_0672 :
    runLexMassChunk 5730 16 checkpoint0656 = checkpoint0672 := by
  decide +kernel

theorem values0656_0672 :
    checkpoint0656.value 5730 = checkpoint0672.value 5730 :=
  runLexMassChunk_value_of_check 5730 16
    checkpoint0656 checkpoint0672 transition0656_0672

#print axioms transition0656_0672
theorem transition0672_0688 :
    runLexMassChunk 5730 16 checkpoint0672 = checkpoint0688 := by
  decide +kernel

theorem values0672_0688 :
    checkpoint0672.value 5730 = checkpoint0688.value 5730 :=
  runLexMassChunk_value_of_check 5730 16
    checkpoint0672 checkpoint0688 transition0672_0688

#print axioms transition0672_0688
theorem transition0688_0704 :
    runLexMassChunk 5730 16 checkpoint0688 = checkpoint0704 := by
  decide +kernel

theorem values0688_0704 :
    checkpoint0688.value 5730 = checkpoint0704.value 5730 :=
  runLexMassChunk_value_of_check 5730 16
    checkpoint0688 checkpoint0704 transition0688_0704

#print axioms transition0688_0704

end Universality.Certificates.MassChunksBase739
