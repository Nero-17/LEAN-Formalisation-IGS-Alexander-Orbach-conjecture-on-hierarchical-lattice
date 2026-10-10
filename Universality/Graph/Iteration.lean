import Universality.Graph.Rule
import Universality.Graph.SubstitutionDistance
import Universality.Percolation.ReliabilityDerivative
import Mathlib.Analysis.Calculus.Deriv.Comp

namespace Universality.Rule
noncomputable section

/-- Index zero is the first rule graph; index n contains n+1 substitutions. -/
def generation (rule : Rule) : ℕ → Rule
  | 0 => rule
  | n + 1 => generation rule n * rule

theorem generation_edges (rule : Rule) (n : ℕ) :
    (rule.generation n).edges = rule.edges ^ (n + 1) := by
  induction n with
  | zero => simp [generation]
  | succ n ih => simp only [generation, mul_edges, ih, pow_succ]

theorem generation_fixed_point (rule : Rule) (p : ℝ)
    (hfixed : rule.network.reliability p = p) (n : ℕ) :
    (rule.generation n).network.reliability p = p := by
  induction n with
  | zero => exact hfixed
  | succ n ih => rw [generation, mul_reliability, hfixed, ih]

theorem generation_hasDerivAt (rule : Rule) (p : ℝ)
    (hfixed : rule.network.reliability p = p) (n : ℕ) :
    HasDerivAt (rule.generation n).network.reliability
      (deriv rule.network.reliability p ^ (n + 1)) p := by
  have hbase : HasDerivAt rule.network.reliability (deriv rule.network.reliability p) p :=
    (rule.network.hasDerivAt_reliability p).differentiableAt.hasDerivAt
  induction n with
  | zero => simpa only [zero_add, pow_one, generation] using hbase
  | succ n ih =>
      have houter : HasDerivAt (rule.generation n).network.reliability
          (deriv rule.network.reliability p ^ (n + 1)) (rule.network.reliability p) := by
        rwa [hfixed]
      have h := houter.comp p hbase
      have hfunction : (rule.generation (n + 1)).network.reliability =
          fun p => (rule.generation n).network.reliability (rule.network.reliability p) := by
        funext p
        exact mul_reliability _ _ p
      rw [hfunction, pow_succ]
      exact h

def generationDistanceCertificate (rule : Rule)
    (certificate : rule.network.DistanceCertificate) :
    (n : ℕ) → (rule.generation n).network.DistanceCertificate
  | 0 => certificate
  | n + 1 => (generationDistanceCertificate rule certificate n).substitute
      (rule.generation n).network rule.network certificate

theorem generationDistanceCertificate_length (rule : Rule)
    (certificate : rule.network.DistanceCertificate) (n : ℕ) :
    (rule.generationDistanceCertificate certificate n).length = certificate.length ^ (n + 1) := by
  induction n with
  | zero => simp [generationDistanceCertificate]
  | succ n ih =>
      change (rule.generationDistanceCertificate certificate n).length * certificate.length = _
      rw [ih, ← pow_succ]

theorem generation_terminal_distance (rule : Rule)
    (reachable : rule.network.fullGraph.Reachable rule.network.source rule.network.target) (n : ℕ) :
    (rule.generation n).network.fullGraph.dist
      (rule.generation n).network.source (rule.generation n).network.target =
      rule.network.fullGraph.dist rule.network.source rule.network.target ^ (n + 1) := by
  rw [(rule.generationDistanceCertificate
    (FiniteNetwork.DistanceCertificate.ofReachable rule.network reachable) n).distance_eq,
    generationDistanceCertificate_length]
  rfl

theorem generation_massMatrix (rule : Rule) (p : ℝ)
    (hfixed : rule.network.reliability p = p) (hp : 0 < p) (hp' : p < 1)
    (symmetry : rule.network.NetworkSymmetry)
    (hs : symmetry.vertex rule.network.source = rule.network.target)
    (ht : symmetry.vertex rule.network.target = rule.network.source) (n : ℕ) :
    (rule.generation n).network.massMatrix p = rule.network.massMatrix p ^ (n + 1) := by
  induction n with
  | zero => simp [generation]
  | succ n ih =>
      rw [generation, mul_massMatrix _ _ p (by rwa [hfixed]) (by rwa [hfixed]) symmetry hs ht,
        hfixed, ih, ← pow_succ]

end
end Universality.Rule
