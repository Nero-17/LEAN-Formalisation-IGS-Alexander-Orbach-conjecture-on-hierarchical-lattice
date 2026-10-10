import Universality.Graph.SubstitutionNetwork

namespace Universality
noncomputable section

/-- A finite network with its size carried as data, so different rule sizes
can be arguments of a single scalar observation. -/
structure Rule where
  vertices : ℕ
  edges : ℕ
  network : FiniteNetwork vertices edges

namespace Rule

def substitute (outer inner : Rule) : Rule where
  vertices := Fintype.card (outer.network.SubstitutionVertex inner.network)
  edges := outer.edges * inner.edges
  network := outer.network.substitute inner.network

instance : Mul Rule := ⟨substitute⟩

theorem mul_edges (outer inner : Rule) : (outer * inner).edges = outer.edges * inner.edges := rfl

theorem mul_reliability (outer inner : Rule) (p : ℝ) :
    (outer * inner).network.reliability p =
      outer.network.reliability (inner.network.reliability p) :=
  outer.network.substitute_reliability inner.network p

theorem mul_massMatrix (outer inner : Rule) (p : ℝ)
    (hpositive : 0 < inner.network.reliability p) (hless : inner.network.reliability p < 1)
    (symmetry : inner.network.NetworkSymmetry)
    (hs : symmetry.vertex inner.network.source = inner.network.target)
    (ht : symmetry.vertex inner.network.target = inner.network.source) :
    (outer * inner).network.massMatrix p =
      outer.network.massMatrix (inner.network.reliability p) * inner.network.massMatrix p :=
  outer.network.substitute_massMatrix_mul inner.network p hpositive hless symmetry hs ht

end Rule
end
end Universality
