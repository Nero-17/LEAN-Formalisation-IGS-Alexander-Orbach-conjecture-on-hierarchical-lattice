import Universality.Graph.CyclicSubstitution
import Universality.Graph.SubstitutionConnectivity
import Universality.Percolation.FiniteCore
import Universality.Matrix.CriticalSimilarity

namespace Universality.Rule
noncomputable section
open Matrix FiniteNetwork
set_option maxHeartbeats 0

/-- Two factors may have distance or cut one. Only their cyclic composites
need the admissibility hypotheses, as in the tie--gem example. -/
theorem cyclic_substitution_real_similarity (outer inner : Rule)
    (houter : outer.TerminalSymmetric) (hinner : inner.TerminalSymmetric)
    (hinnerConnected : inner.network.fullGraph.Reachable inner.network.source inner.network.target)
    (hforward : (outer * inner).MassAdmissible) (hbackward : (inner * outer).MassAdmissible)
    (p : ℝ) (hp : 0 < p) (hp' : p < 1) (hfixed : (outer * inner).network.reliability p = p) :
    ∃ basis inverse : Matrix LiveState LiveState ℝ,
      inverse * basis = 1 ∧ basis * inverse = 1 ∧
      inverse * (outer * inner).network.massMatrix p * basis =
        (inner * outer).network.massMatrix (inner.network.reliability p) := by
  obtain ⟨outerSymmetry, hos, hot⟩ := houter
  obtain ⟨innerSymmetry, his, hit⟩ := hinner
  obtain ⟨forwardSymmetry, hfs, hft⟩ := hforward.symmetric
  obtain ⟨backwardSymmetry, hbs, hbt⟩ := hbackward.symmetric
  have hpositive := (inner.network.reliability_pos_iff_connected hp hp').mpr hinnerConnected
  have hless := inner.network.reliability_lt_one hp hp'
  have hreverse := cyclic_substitution_fixed_point outer inner p hfixed
  have hresponse := cyclic_substitution_response outer inner p hfixed
  have hfixed' : outer.network.reliability (inner.network.reliability p) = p := by
    simpa only [mul_reliability] using hfixed
  have hfirst := mul_massMatrix outer inner p hpositive hless innerSymmetry his hit
  have hsecond := mul_massMatrix inner outer (inner.network.reliability p)
    (by rwa [hfixed']) (by rwa [hfixed']) outerSymmetry hos hot
  rw [hfixed'] at hsecond
  have hplaneInner := inner.network.massMatrix_preservesMassPlane p innerSymmetry his hit
  have hplaneOuter := outer.network.massMatrix_preservesMassPlane
    (inner.network.reliability p) outerSymmetry hos hot
  apply real_similarity_of_critical_blocks _ _ p (inner.network.reliability p)
    (deriv (outer * inner).network.reliability p) hp.ne' hpositive.ne'
    ((outer * inner).network.massMatrix_preservesMassPlane p forwardSymmetry hfs hft)
    ((inner * outer).network.massMatrix_preservesMassPlane _ backwardSymmetry hbs hbt)
    ((outer * inner).network.pivotal_right_eigenvector_at_fixed_point p hfixed hp.ne' hp'.ne
      forwardSymmetry hfs hft)
  · rw [hresponse]
    exact (inner * outer).network.pivotal_right_eigenvector_at_fixed_point _ hreverse
      hpositive.ne' hless.ne backwardSymmetry hbs hbt
  · exact ((outer * inner).network.massPlaneBlock_pos_of_geometry hp hp'
      hforward.connected hforward.scale hforward.cut).1
  · exact ((inner * outer).network.massPlaneBlock_pos_of_geometry hpositive hless
      hbackward.connected hbackward.scale hbackward.cut).1
  · rw [hfirst, hsecond, massPlaneBlock_mul _ _ hplaneInner, massPlaneBlock_mul _ _ hplaneOuter]
    exact Matrix.trace_mul_comm _ _
  · rw [hfirst, hsecond, massPlaneBlock_mul _ _ hplaneInner, massPlaneBlock_mul _ _ hplaneOuter,
      Matrix.det_mul, Matrix.det_mul, mul_comm]

end
end Universality.Rule
