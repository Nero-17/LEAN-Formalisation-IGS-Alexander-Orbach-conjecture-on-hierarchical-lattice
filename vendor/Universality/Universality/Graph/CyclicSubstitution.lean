import Universality.Algebra.CyclicInvariance
import Universality.Graph.Rule
import Universality.Graph.SubstitutionDistance
import Universality.Percolation.UniqueFixedPoint

/-!
The cyclic identities below concern actual substituted finite networks.
They do not presuppose that mass matrices or reliability polynomials commute.
The occupation parameter changes from p to the inner crossing probability.
-/

namespace Universality.Rule
noncomputable section

theorem cyclic_substitution_edges (outer inner : Rule) :
    (outer * inner).edges = (inner * outer).edges := by
  simp only [mul_edges, Nat.mul_comm]

theorem cyclic_substitution_distance (outer inner : Rule)
    (houter : outer.network.fullGraph.Reachable outer.network.source outer.network.target)
    (hinner : inner.network.fullGraph.Reachable inner.network.source inner.network.target) :
    (outer * inner).network.fullGraph.dist
        (outer * inner).network.source (outer * inner).network.target =
      (inner * outer).network.fullGraph.dist
        (inner * outer).network.source (inner * outer).network.target := by
  change (outer.network.substitute inner.network).fullGraph.dist
      (outer.network.substitute inner.network).source
      (outer.network.substitute inner.network).target =
    (inner.network.substitute outer.network).fullGraph.dist
      (inner.network.substitute outer.network).source
      (inner.network.substitute outer.network).target
  rw [FiniteNetwork.substitute_terminal_distance _ _ houter hinner,
    FiniteNetwork.substitute_terminal_distance _ _ hinner houter, Nat.mul_comm]

theorem cyclic_substitution_fixed_point (outer inner : Rule) (p : ℝ)
    (hfixed : (outer * inner).network.reliability p = p) :
    (inner * outer).network.reliability (inner.network.reliability p) =
      inner.network.reliability p := by
  rw [mul_reliability] at hfixed ⊢
  rw [hfixed]

theorem cyclic_substitution_response (outer inner : Rule) (p : ℝ)
    (hfixed : (outer * inner).network.reliability p = p) :
    deriv (outer * inner).network.reliability p =
      deriv (inner * outer).network.reliability (inner.network.reliability p) := by
  have hcomposition : (outer * inner).network.reliability =
      fun x => outer.network.reliability (inner.network.reliability x) :=
    funext (mul_reliability outer inner)
  have hreverse : (inner * outer).network.reliability =
      fun x => inner.network.reliability (outer.network.reliability x) :=
    funext (mul_reliability inner outer)
  rw [mul_reliability] at hfixed
  have h := cyclic_derivative_multiplier outer.network.reliability inner.network.reliability
    p (deriv outer.network.reliability (inner.network.reliability p))
    (deriv inner.network.reliability p) hfixed
    (outer.network.hasDerivAt_reliability _).differentiableAt.hasDerivAt
    (inner.network.hasDerivAt_reliability _).differentiableAt.hasDerivAt
  rw [hcomposition, hreverse, h.1.deriv, h.2.deriv]

theorem cyclic_substitution_spectralRadius (outer inner : Rule) (p : ℝ)
    (hp : 0 < p) (hp' : p < 1)
    (hinner : inner.network.fullGraph.Reachable inner.network.source inner.network.target)
    (hfixed : (outer * inner).network.reliability p = p)
    (outerSymmetry : outer.network.NetworkSymmetry)
    (hos : outerSymmetry.vertex outer.network.source = outer.network.target)
    (hot : outerSymmetry.vertex outer.network.target = outer.network.source)
    (innerSymmetry : inner.network.NetworkSymmetry)
    (his : innerSymmetry.vertex inner.network.source = inner.network.target)
    (hit : innerSymmetry.vertex inner.network.target = inner.network.source) :
    spectralRadius ℂ (((outer * inner).network.massMatrix p).map Complex.ofReal) =
      spectralRadius ℂ (((inner * outer).network.massMatrix
        (inner.network.reliability p)).map Complex.ofReal) := by
  rw [mul_reliability] at hfixed
  have hpositive := (inner.network.reliability_pos_iff_connected hp hp').mpr hinner
  have hless := inner.network.reliability_lt_one hp hp'
  rw [mul_massMatrix outer inner p hpositive hless innerSymmetry his hit,
    mul_massMatrix inner outer (inner.network.reliability p)
      (by rwa [hfixed]) (by rwa [hfixed]) outerSymmetry hos hot, hfixed]
  change spectralRadius ℂ ((Complex.ofRealHom.mapMatrix)
      (outer.network.massMatrix (inner.network.reliability p) * inner.network.massMatrix p)) =
    spectralRadius ℂ ((Complex.ofRealHom.mapMatrix)
      (inner.network.massMatrix p * outer.network.massMatrix (inner.network.reliability p)))
  rw [map_mul, map_mul, cyclic_spectralRadius_eq]

end
end Universality.Rule
