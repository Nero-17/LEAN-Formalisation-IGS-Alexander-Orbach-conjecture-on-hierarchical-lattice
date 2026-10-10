import Universality.Certificates.Section5MassChunkDataBase66112
import Universality.Certificates.Section5MassChunkDataBase66111

namespace Universality.Certificates.MassChunksBase661

set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option exponentiation.threshold 10000
set_option Elab.async false

theorem transition0816_0832 :
    runLexMassChunk 5634 16 checkpoint0816 = checkpoint0832 := by
  decide +kernel

theorem values0816_0832 :
    checkpoint0816.value 5634 = checkpoint0832.value 5634 :=
  runLexMassChunk_value_of_check 5634 16
    checkpoint0816 checkpoint0832 transition0816_0832

#print axioms transition0816_0832

end Universality.Certificates.MassChunksBase661
