import Universality.Certificates.Section5MassChunkDataBase73911
import Universality.Certificates.Section5MassChunkDataBase73910

namespace Universality.Certificates.MassChunksBase739

set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option exponentiation.threshold 10000
set_option Elab.async false

theorem transition0704_0720 :
    runLexMassChunk 5730 16 checkpoint0704 = checkpoint0720 := by
  decide +kernel

theorem values0704_0720 :
    checkpoint0704.value 5730 = checkpoint0720.value 5730 :=
  runLexMassChunk_value_of_check 5730 16
    checkpoint0704 checkpoint0720 transition0704_0720

#print axioms transition0704_0720
theorem transition0720_0736 :
    runLexMassChunk 5730 16 checkpoint0720 = checkpoint0736 := by
  decide +kernel

theorem values0720_0736 :
    checkpoint0720.value 5730 = checkpoint0736.value 5730 :=
  runLexMassChunk_value_of_check 5730 16
    checkpoint0720 checkpoint0736 transition0720_0736

#print axioms transition0720_0736
theorem transition0736_0752 :
    runLexMassChunk 5730 16 checkpoint0736 = checkpoint0752 := by
  decide +kernel

theorem values0736_0752 :
    checkpoint0736.value 5730 = checkpoint0752.value 5730 :=
  runLexMassChunk_value_of_check 5730 16
    checkpoint0736 checkpoint0752 transition0736_0752

#print axioms transition0736_0752
theorem transition0752_0768 :
    runLexMassChunk 5730 16 checkpoint0752 = checkpoint0768 := by
  decide +kernel

theorem values0752_0768 :
    checkpoint0752.value 5730 = checkpoint0768.value 5730 :=
  runLexMassChunk_value_of_check 5730 16
    checkpoint0752 checkpoint0768 transition0752_0768

#print axioms transition0752_0768

end Universality.Certificates.MassChunksBase739
