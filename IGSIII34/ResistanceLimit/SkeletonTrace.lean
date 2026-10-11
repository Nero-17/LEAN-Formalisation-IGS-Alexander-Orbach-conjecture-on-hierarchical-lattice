import IGSIII34.ResistanceLimit.PairContinuity
import IGSIII34.ResistanceLimit.PairTrace
import IGSIII34.Percolation.ElectricalTree

set_option autoImplicit false
set_option maxHeartbeats 1800000
namespace IGSIII34.ResistanceLimit
noncomputable section
open Universality Universality.FiniteNetwork IGSIII34.Percolation
open Resistance Resistance.FiniteNetwork Filter
open scoped Topology

variable {outerVertices outerEdges innerVertices innerEdges : ℕ}

/-- Exact elimination in the actual numbered substituted network, for every
coarse pair. The trace includes every crossing edge in dangling branches. -/
theorem actual_substitution_scaled_pairResistance_trace
    (outer : Universality.FiniteNetwork outerVertices outerEdges)
    (inner : Universality.FiniteNetwork innerVertices innerEdges)
    (configuration : Fin outerEdges → Configuration innerEdges)
    (scalar : ℝ) (scalarNonnegative : 0 ≤ scalar)
    (first last : Fin outerVertices)
    (reachable : (outer.openGraph (inner.coarseConfiguration configuration)).Reachable first last) :
    scalar * pairResistance (network (outer.substitute inner) (substitutionConfigurationEquiv configuration))
      (fun _ => 1)
      (Fintype.equivFin _ (Sum.inl first : outer.SubstitutionVertex inner))
      (Fintype.equivFin _ (Sum.inl last : outer.SubstitutionVertex inner)) =
      pairResistance (network outer (inner.coarseConfiguration configuration))
        (fun edge => scalar * unitConfigurationResistance inner (configuration edge.val)) first last := by
  have trace := actual_substitution_pairResistance_trace outer inner configuration
    (fun _ => 1) (fun _ => zero_lt_one) first last reachable
  have scaled := congrArg (fun value : ℝ => scalar * value) trace
  have homogeneity := pairResistance_scale (network outer (inner.coarseConfiguration configuration))
    (coarseResistance inner configuration (fun _ => 1))
    (fun edge => (coarseResistance_positive inner configuration (fun _ => 1) (fun _ => zero_lt_one) edge).le)
    scalar scalarNonnegative first last
  exact scaled.trans homogeneity.symm

end
end IGSIII34.ResistanceLimit
