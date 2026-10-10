import Universality.Certificates.Section5RowsShifted19
import Universality.Certificates.Section5DisjointShifted19
import Universality.Certificates.Section5PacketCapacityShifted19

namespace Universality.Certificates

set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option exponentiation.threshold 4096

theorem allocationShifted19_capacityValid : allocationShifted19.capacityValid :=
  ⟨by decide +kernel, by decide +kernel, by decide +kernel, allocationShifted19_initial_slacks,
    allocationShifted19_disjoint, allocationShifted19_packet_checks⟩

theorem allocationShifted19_capacity (word : List Bool)
    (length_checked : word.length = 424) :
    allocationShifted19.allocation word ≤ 2 ^ zeroCount word :=
  allocationShifted19.allocation_capacity allocationShifted19_capacityValid word length_checked

end Universality.Certificates
