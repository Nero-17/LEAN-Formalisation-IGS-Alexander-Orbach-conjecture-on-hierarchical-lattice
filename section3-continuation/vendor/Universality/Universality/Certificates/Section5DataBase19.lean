import Universality.Certificates.Section5RowsBase19
import Universality.Certificates.Section5DisjointBase19
import Universality.Certificates.Section5PacketCapacityBase19

namespace Universality.Certificates

set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option exponentiation.threshold 4096

theorem allocationBase19_capacityValid : allocationBase19.capacityValid :=
  ⟨by decide +kernel, by decide +kernel, by decide +kernel, allocationBase19_initial_slacks,
    allocationBase19_disjoint, allocationBase19_packet_checks⟩

theorem allocationBase19_capacity (word : List Bool)
    (length_checked : word.length = 424) :
    allocationBase19.allocation word ≤ 2 ^ zeroCount word :=
  allocationBase19.allocation_capacity allocationBase19_capacityValid word length_checked

end Universality.Certificates
