import Universality.Certificates.Section5RowsBase739
import Universality.Certificates.Section5DisjointBase739
import Universality.Certificates.Section5PacketCapacityBase739

namespace Universality.Certificates

set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option exponentiation.threshold 4096

theorem allocationBase739_capacityValid : allocationBase739.capacityValid :=
  ⟨by decide +kernel, by decide +kernel, by decide +kernel, allocationBase739_initial_slacks,
    allocationBase739_disjoint, allocationBase739_packet_checks⟩

theorem allocationBase739_capacity (word : List Bool)
    (length_checked : word.length = 952) :
    allocationBase739.allocation word ≤ 2 ^ zeroCount word :=
  allocationBase739.allocation_capacity allocationBase739_capacityValid word length_checked

end Universality.Certificates
