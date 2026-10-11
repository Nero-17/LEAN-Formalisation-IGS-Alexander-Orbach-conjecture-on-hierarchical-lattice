import Universality.Certificates.Section5MassChunkDataBase66112
import Universality.Certificates.Section5MassChunkDataBase66111

namespace Universality.Certificates.MassChunksBase661

set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option exponentiation.threshold 10000
set_option Elab.async false

theorem transition0800_0816 :
    runLexMassChunk 5634 16 checkpoint0800 = checkpoint0816 := by
  decide +kernel

theorem values0800_0816 :
    checkpoint0800.value 5634 = checkpoint0816.value 5634 :=
  runLexMassChunk_value_of_check 5634 16
    checkpoint0800 checkpoint0816 transition0800_0816

#print axioms transition0800_0816

end Universality.Certificates.MassChunksBase661
