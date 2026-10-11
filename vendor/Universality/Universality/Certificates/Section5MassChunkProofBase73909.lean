import Universality.Certificates.Section5MassChunkDataBase73909
import Universality.Certificates.Section5MassChunkDataBase73908

namespace Universality.Certificates.MassChunksBase739

set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option exponentiation.threshold 10000
set_option Elab.async false

theorem transition0576_0592 :
    runLexMassChunk 5730 16 checkpoint0576 = checkpoint0592 := by
  decide +kernel

theorem values0576_0592 :
    checkpoint0576.value 5730 = checkpoint0592.value 5730 :=
  runLexMassChunk_value_of_check 5730 16
    checkpoint0576 checkpoint0592 transition0576_0592

#print axioms transition0576_0592
theorem transition0592_0608 :
    runLexMassChunk 5730 16 checkpoint0592 = checkpoint0608 := by
  decide +kernel

theorem values0592_0608 :
    checkpoint0592.value 5730 = checkpoint0608.value 5730 :=
  runLexMassChunk_value_of_check 5730 16
    checkpoint0592 checkpoint0608 transition0592_0608

#print axioms transition0592_0608
theorem transition0608_0624 :
    runLexMassChunk 5730 16 checkpoint0608 = checkpoint0624 := by
  decide +kernel

theorem values0608_0624 :
    checkpoint0608.value 5730 = checkpoint0624.value 5730 :=
  runLexMassChunk_value_of_check 5730 16
    checkpoint0608 checkpoint0624 transition0608_0624

#print axioms transition0608_0624
theorem transition0624_0640 :
    runLexMassChunk 5730 16 checkpoint0624 = checkpoint0640 := by
  decide +kernel

theorem values0624_0640 :
    checkpoint0624.value 5730 = checkpoint0640.value 5730 :=
  runLexMassChunk_value_of_check 5730 16
    checkpoint0624 checkpoint0640 transition0624_0640

#print axioms transition0624_0640

end Universality.Certificates.MassChunksBase739
