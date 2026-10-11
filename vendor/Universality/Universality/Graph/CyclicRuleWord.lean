import Universality.Graph.RuleWord
import Universality.Percolation.MassMatrixEquivalence
import Universality.Graph.CyclicSimilarity
import Universality.Graph.SubstitutionPotential

namespace Universality.FiniteNetwork.NetworkEquivalence
noncomputable section
variable {vR eR vS eS : ℕ} {R : FiniteNetwork vR eR} {S : FiniteNetwork vS eS}

def fullGraphIso (equivalence : R.NetworkEquivalence S) : R.fullGraph ≃g S.fullGraph :=
  equivalence.openGraphIso (fun _ => true)

theorem terminal_distance (equivalence : R.NetworkEquivalence S)
    (hconnected : R.fullGraph.Reachable R.source R.target) :
    S.fullGraph.dist S.source S.target = R.fullGraph.dist R.source R.target := by
  have h := graph_iso_distance_of_reachable equivalence.fullGraphIso hconnected
  change S.fullGraph.dist (equivalence.vertex R.source) (equivalence.vertex R.target) = _ at h
  simpa only [equivalence.source, equivalence.target] using h

end
end Universality.FiniteNetwork.NetworkEquivalence

namespace Universality.Rule
noncomputable section
open FiniteNetwork Matrix
set_option maxHeartbeats 0

theorem cyclic_word_fixed_point (first : Rule) (middle : List Rule) (last : Rule) (p : ℝ)
    (hfixed : (word (first :: middle) last).network.reliability p = p) :
    (word (middle ++ [last]) first).network.reliability ((word middle last).network.reliability p) =
      (word middle last).network.reliability p := by
  rw [← (wordRotateEquivalence first middle last).reliability]
  exact cyclic_substitution_fixed_point first (word middle last) p hfixed

theorem cyclic_word_response (first : Rule) (middle : List Rule) (last : Rule) (p : ℝ)
    (hfixed : (word (first :: middle) last).network.reliability p = p) :
    deriv (word (first :: middle) last).network.reliability p =
      deriv (word (middle ++ [last]) first).network.reliability ((word middle last).network.reliability p) := by
  have heq := funext (wordRotateEquivalence first middle last).reliability
  rw [← heq]
  exact cyclic_substitution_response first (word middle last) p hfixed

theorem cyclic_word_edges (first : Rule) (middle : List Rule) (last : Rule) :
    (word (first :: middle) last).edges = (word (middle ++ [last]) first).edges := by
  simp only [word_edges, List.map_cons, List.prod_cons, List.map_append,
    List.prod_append, List.map_singleton, List.prod_singleton]
  ac_rfl

theorem cyclic_word_distance (first : Rule) (middle : List Rule) (last : Rule)
    (hfirst : first.network.fullGraph.Reachable first.network.source first.network.target)
    (hmiddle : ∀ rule ∈ middle, rule.network.fullGraph.Reachable rule.network.source rule.network.target)
    (hlast : last.network.fullGraph.Reachable last.network.source last.network.target) :
    (word (first :: middle) last).network.fullGraph.dist
      (word (first :: middle) last).network.source (word (first :: middle) last).network.target =
    (word (middle ++ [last]) first).network.fullGraph.dist
      (word (middle ++ [last]) first).network.source (word (middle ++ [last]) first).network.target := by
  have hrest := word_connected middle last hmiddle hlast
  have hrotated := word_connected (middle ++ [last]) first
    (by intro rule hrule; rcases List.mem_append.mp hrule with h | h
        · exact hmiddle rule h
        · have heq := List.mem_singleton.mp h
          subst rule
          exact hlast) hfirst
  rw [← (wordRotateEquivalence first middle last).terminal_distance hrotated]
  exact cyclic_substitution_distance first (word middle last) hfirst hrest

theorem cyclic_word_spectralRadius (first : Rule) (middle : List Rule) (last : Rule)
    (hfirst : first.TerminalSymmetric)
    (hmiddle : ∀ rule ∈ middle, rule.TerminalSymmetric) (hlast : last.TerminalSymmetric)
    (hconnected : (word middle last).network.fullGraph.Reachable
      (word middle last).network.source (word middle last).network.target)
    (p : ℝ) (hp : 0 < p) (hp' : p < 1)
    (hfixed : (word (first :: middle) last).network.reliability p = p) :
    spectralRadius ℂ (((word (first :: middle) last).network.massMatrix p).map Complex.ofReal) =
      spectralRadius ℂ (((word (middle ++ [last]) first).network.massMatrix
        ((word middle last).network.reliability p)).map Complex.ofReal) := by
  obtain ⟨firstSymmetry, hfs, hft⟩ := hfirst
  obtain ⟨restSymmetry, hrs, hrt⟩ := word_terminalSymmetric middle last hmiddle hlast
  rw [← (wordRotateEquivalence first middle last).massMatrix]
  exact cyclic_substitution_spectralRadius first (word middle last) p hp hp' hconnected hfixed
    firstSymmetry hfs hft restSymmetry hrs hrt

theorem cyclic_word_real_similarity (first : Rule) (middle : List Rule) (last : Rule)
    (hfirst : first.TerminalSymmetric)
    (hmiddle : ∀ rule ∈ middle, rule.TerminalSymmetric) (hlast : last.TerminalSymmetric)
    (hconnected : (word middle last).network.fullGraph.Reachable
      (word middle last).network.source (word middle last).network.target)
    (hforward : (word (first :: middle) last).MassAdmissible)
    (hbackward : (word (middle ++ [last]) first).MassAdmissible)
    (p : ℝ) (hp : 0 < p) (hp' : p < 1)
    (hfixed : (word (first :: middle) last).network.reliability p = p) :
    ∃ basis inverse : Matrix LiveState LiveState ℝ,
      inverse * basis = 1 ∧ basis * inverse = 1 ∧
      inverse * (word (first :: middle) last).network.massMatrix p * basis =
        (word (middle ++ [last]) first).network.massMatrix ((word middle last).network.reliability p) := by
  obtain ⟨firstSymmetry, hfs, hft⟩ := hfirst
  obtain ⟨restSymmetry, hrs, hrt⟩ := word_terminalSymmetric middle last hmiddle hlast
  obtain ⟨forwardSymmetry, hforwardSource, hforwardTarget⟩ := hforward.symmetric
  obtain ⟨backwardSymmetry, hbackwardSource, hbackwardTarget⟩ := hbackward.symmetric
  have hpositive := ((word middle last).network.reliability_pos_iff_connected hp hp').mpr hconnected
  have hless := (word middle last).network.reliability_lt_one hp hp'
  have hreverse := cyclic_word_fixed_point first middle last p hfixed
  have hresponse := cyclic_word_response first middle last p hfixed
  have hfixed' : first.network.reliability ((word middle last).network.reliability p) = p := by
    simpa only [word, mul_reliability] using hfixed
  have hmatrixFirst := mul_massMatrix first (word middle last) p hpositive hless restSymmetry hrs hrt
  have hmatrixSecond := mul_massMatrix (word middle last) first ((word middle last).network.reliability p)
    (by rwa [hfixed']) (by rwa [hfixed']) firstSymmetry hfs hft
  rw [hfixed', (wordRotateEquivalence first middle last).massMatrix] at hmatrixSecond
  have hplaneRest := (word middle last).network.massMatrix_preservesMassPlane p restSymmetry hrs hrt
  have hplaneFirst := first.network.massMatrix_preservesMassPlane
    ((word middle last).network.reliability p) firstSymmetry hfs hft
  apply real_similarity_of_critical_blocks _ _ p ((word middle last).network.reliability p)
    (deriv (word (first :: middle) last).network.reliability p) hp.ne' hpositive.ne'
    ((word (first :: middle) last).network.massMatrix_preservesMassPlane p forwardSymmetry
      hforwardSource hforwardTarget)
    ((word (middle ++ [last]) first).network.massMatrix_preservesMassPlane _ backwardSymmetry
      hbackwardSource hbackwardTarget)
    ((word (first :: middle) last).network.pivotal_right_eigenvector_at_fixed_point p hfixed
      hp.ne' hp'.ne forwardSymmetry hforwardSource hforwardTarget)
  · rw [hresponse]
    exact (word (middle ++ [last]) first).network.pivotal_right_eigenvector_at_fixed_point _ hreverse
      hpositive.ne' hless.ne backwardSymmetry hbackwardSource hbackwardTarget
  · exact ((word (first :: middle) last).network.massPlaneBlock_pos_of_geometry hp hp'
      hforward.connected hforward.scale hforward.cut).1
  · exact ((word (middle ++ [last]) first).network.massPlaneBlock_pos_of_geometry hpositive hless
      hbackward.connected hbackward.scale hbackward.cut).1
  · change (massPlaneBlock ((first * word middle last).network.massMatrix p)).trace = _
    rw [hmatrixFirst, hmatrixSecond, massPlaneBlock_mul _ _ hplaneRest,
      massPlaneBlock_mul _ _ hplaneFirst]
    exact Matrix.trace_mul_comm _ _
  · change (massPlaneBlock ((first * word middle last).network.massMatrix p)).det = _
    rw [hmatrixFirst, hmatrixSecond, massPlaneBlock_mul _ _ hplaneRest,
      massPlaneBlock_mul _ _ hplaneFirst, Matrix.det_mul, Matrix.det_mul, mul_comm]

end
end Universality.Rule
