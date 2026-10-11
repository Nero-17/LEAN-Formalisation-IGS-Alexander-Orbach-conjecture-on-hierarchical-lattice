import Universality.Certificates.Section5RowsBase661
import Universality.Certificates.Section5DisjointBase661
import Universality.Certificates.Section5PacketCapacityBase661

namespace Universality.Certificates

set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option exponentiation.threshold 4096

theorem allocationBase661_capacityValid : allocationBase661.capacityValid :=
  ⟨by decide +kernel, by decide +kernel, by decide +kernel, allocationBase661_initial_slacks,
    allocationBase661_disjoint, allocationBase661_packet_checks⟩

theorem allocationBase661_capacity (word : List Bool)
    (length_checked : word.length = 936) :
    allocationBase661.allocation word ≤ 2 ^ zeroCount word :=
  allocationBase661.allocation_capacity allocationBase661_capacityValid word length_checked

end Universality.Certificates
