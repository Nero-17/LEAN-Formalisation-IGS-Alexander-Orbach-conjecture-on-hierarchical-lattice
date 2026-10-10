import Universality.Certificates.Section5MassChunkDataBase73912
import Universality.Certificates.Section5MassChunkDataBase73911

namespace Universality.Certificates.MassChunksBase739

set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option exponentiation.threshold 10000
set_option Elab.async false

theorem transition0768_0784 :
    runLexMassChunk 5730 16 checkpoint0768 = checkpoint0784 := by
  decide +kernel

theorem values0768_0784 :
    checkpoint0768.value 5730 = checkpoint0784.value 5730 :=
  runLexMassChunk_value_of_check 5730 16
    checkpoint0768 checkpoint0784 transition0768_0784

#print axioms transition0768_0784
theorem transition0784_0800 :
    runLexMassChunk 5730 16 checkpoint0784 = checkpoint0800 := by
  decide +kernel

theorem values0784_0800 :
    checkpoint0784.value 5730 = checkpoint0800.value 5730 :=
  runLexMassChunk_value_of_check 5730 16
    checkpoint0784 checkpoint0800 transition0784_0800

#print axioms transition0784_0800
theorem transition0800_0816 :
    runLexMassChunk 5730 16 checkpoint0800 = checkpoint0816 := by
  decide +kernel

theorem values0800_0816 :
    checkpoint0800.value 5730 = checkpoint0816.value 5730 :=
  runLexMassChunk_value_of_check 5730 16
    checkpoint0800 checkpoint0816 transition0800_0816

#print axioms transition0800_0816
theorem transition0816_0832 :
    runLexMassChunk 5730 16 checkpoint0816 = checkpoint0832 := by
  decide +kernel

theorem values0816_0832 :
    checkpoint0816.value 5730 = checkpoint0832.value 5730 :=
  runLexMassChunk_value_of_check 5730 16
    checkpoint0816 checkpoint0832 transition0816_0832

#print axioms transition0816_0832

end Universality.Certificates.MassChunksBase739
