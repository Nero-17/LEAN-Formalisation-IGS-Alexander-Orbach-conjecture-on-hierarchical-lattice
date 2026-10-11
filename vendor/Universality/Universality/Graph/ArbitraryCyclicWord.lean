import Universality.Graph.CyclicRuleWord

namespace Universality.Rule
noncomputable section
open FiniteNetwork Matrix
set_option maxHeartbeats 800000
attribute [local irreducible] word
set_option backward.isDefEq.respectTransparency false

theorem cyclic_factor_interior (outer inner : Rule) (p : ℝ) (hp : 0 < p) (hp' : p < 1)
    (hfixed : (outer * inner).network.reliability p = p) :
    0 < inner.network.reliability p ∧ inner.network.reliability p < 1 ∧
      inner.network.fullGraph.Reachable inner.network.source inner.network.target ∧
      outer.network.fullGraph.Reachable outer.network.source outer.network.target := by
  have hpositive : 0 < inner.network.reliability p := by
    by_contra h
    have hzero := le_antisymm (le_of_not_gt h) (inner.network.reliability_nonneg hp.le hp'.le)
    rw [mul_reliability, hzero, outer.network.reliability_zero] at hfixed
    exact hp.ne' hfixed.symm
  have hless := inner.network.reliability_lt_one hp hp'
  refine ⟨hpositive, hless, (inner.network.reliability_pos_iff_connected hp hp').mp hpositive, ?_⟩
  apply (outer.network.reliability_pos_iff_connected hpositive hless).mp
  rw [mul_reliability] at hfixed
  rwa [hfixed]

theorem cyclic_block_word_fixed_point (initial suffix : List Rule) (middle last : Rule) (p : ℝ)
    (hfixed : (word (initial ++ middle :: suffix) last).network.reliability p = p) :
    (word (suffix ++ last :: initial) middle).network.reliability
        ((word suffix last).network.reliability p) = (word suffix last).network.reliability p := by
  rw [← (wordAppendEquivalence initial middle suffix last).reliability] at hfixed
  rw [← (wordAppendEquivalence suffix last initial middle).reliability]
  exact cyclic_substitution_fixed_point (word initial middle) (word suffix last) p hfixed

theorem cyclic_block_word_response (initial suffix : List Rule) (middle last : Rule) (p : ℝ)
    (hfixed : (word (initial ++ middle :: suffix) last).network.reliability p = p) :
    deriv (word (initial ++ middle :: suffix) last).network.reliability p =
      deriv (word (suffix ++ last :: initial) middle).network.reliability
        ((word suffix last).network.reliability p) := by
  have hforward := funext (wordAppendEquivalence initial middle suffix last).reliability
  have hbackward := funext (wordAppendEquivalence suffix last initial middle).reliability
  rw [← hforward] at hfixed ⊢
  rw [← hbackward]
  exact cyclic_substitution_response (word initial middle) (word suffix last) p hfixed

theorem cyclic_block_word_edges (initial suffix : List Rule) (middle last : Rule) :
    (word (initial ++ middle :: suffix) last).edges =
      (word (suffix ++ last :: initial) middle).edges := by
  simp only [word_edges, List.map_append, List.map_cons, List.prod_append, List.prod_cons]
  ac_rfl

theorem cyclic_block_word_distance (initial suffix : List Rule) (middle last : Rule) (p : ℝ)
    (hp : 0 < p) (hp' : p < 1)
    (hfixed : (word (initial ++ middle :: suffix) last).network.reliability p = p) :
    (word (initial ++ middle :: suffix) last).network.fullGraph.dist
        (word (initial ++ middle :: suffix) last).network.source
        (word (initial ++ middle :: suffix) last).network.target =
      (word (suffix ++ last :: initial) middle).network.fullGraph.dist
        (word (suffix ++ last :: initial) middle).network.source
        (word (suffix ++ last :: initial) middle).network.target := by
  have hfactor := hfixed
  rw [← (wordAppendEquivalence initial middle suffix last).reliability] at hfactor
  obtain ⟨hpositive, hless, hinner, houter⟩ := cyclic_factor_interior _ _ p hp hp' hfactor
  have hconnected := ((word (initial ++ middle :: suffix) last).network.reliability_pos_iff_connected hp hp').mp (by rwa [hfixed])
  have hreverse := cyclic_block_word_fixed_point initial suffix middle last p hfixed
  have hconnected' := ((word (suffix ++ last :: initial) middle).network.reliability_pos_iff_connected hpositive hless).mp (by rwa [hreverse])
  rw [← (wordAppendEquivalence initial middle suffix last).terminal_distance hconnected,
    ← (wordAppendEquivalence suffix last initial middle).terminal_distance hconnected']
  exact cyclic_substitution_distance (word initial middle) (word suffix last) houter hinner

theorem cyclic_block_word_spectralRadius (initial suffix : List Rule) (middle last : Rule)
    (hinitial : ∀ rule ∈ initial, rule.TerminalSymmetric) (hmiddle : middle.TerminalSymmetric)
    (hsuffix : ∀ rule ∈ suffix, rule.TerminalSymmetric) (hlast : last.TerminalSymmetric)
    (p : ℝ) (hp : 0 < p) (hp' : p < 1)
    (hfixed : (word (initial ++ middle :: suffix) last).network.reliability p = p) :
    spectralRadius ℂ (((word (initial ++ middle :: suffix) last).network.massMatrix p).map Complex.ofReal) =
      spectralRadius ℂ (((word (suffix ++ last :: initial) middle).network.massMatrix
        ((word suffix last).network.reliability p)).map Complex.ofReal) := by
  rw [← (wordAppendEquivalence initial middle suffix last).reliability] at hfixed
  obtain ⟨_, _, hinner, _⟩ := cyclic_factor_interior _ _ p hp hp' hfixed
  obtain ⟨outerSymmetry, hos, hot⟩ := word_terminalSymmetric initial middle hinitial hmiddle
  obtain ⟨innerSymmetry, his, hit⟩ := word_terminalSymmetric suffix last hsuffix hlast
  rw [← (wordAppendEquivalence initial middle suffix last).massMatrix,
    ← (wordAppendEquivalence suffix last initial middle).massMatrix]
  exact cyclic_substitution_spectralRadius _ _ p hp hp' hinner hfixed outerSymmetry hos hot innerSymmetry his hit

theorem cyclic_block_word_real_similarity (initial suffix : List Rule) (middle last : Rule)
    (hinitial : ∀ rule ∈ initial, rule.TerminalSymmetric) (hmiddle : middle.TerminalSymmetric)
    (hsuffix : ∀ rule ∈ suffix, rule.TerminalSymmetric) (hlast : last.TerminalSymmetric)
    (hscale : 1 < (word (initial ++ middle :: suffix) last).network.fullGraph.dist
      (word (initial ++ middle :: suffix) last).network.source
      (word (initial ++ middle :: suffix) last).network.target)
    (p : ℝ) (hp : 0 < p) (hp' : p < 1)
    (hfixed : (word (initial ++ middle :: suffix) last).network.reliability p = p) :
    ∃ basis inverse : Matrix LiveState LiveState ℝ,
      inverse * basis = 1 ∧ basis * inverse = 1 ∧
      inverse * (word (initial ++ middle :: suffix) last).network.massMatrix p * basis =
        (word (suffix ++ last :: initial) middle).network.massMatrix
          ((word suffix last).network.reliability p) := by
  have hconnected := ((word (initial ++ middle :: suffix) last).network.reliability_pos_iff_connected hp hp').mp (by rwa [hfixed])
  rw [← (wordAppendEquivalence initial middle suffix last).terminal_distance hconnected] at hscale
  rw [← (wordAppendEquivalence initial middle suffix last).reliability] at hfixed
  obtain ⟨hpositive, hless, hinner, houter⟩ := cyclic_factor_interior _ _ p hp hp' hfixed
  have houterSymmetric := word_terminalSymmetric initial middle hinitial hmiddle
  have hinnerSymmetric := word_terminalSymmetric suffix last hsuffix hlast
  have hscale' := hscale
  rw [cyclic_substitution_distance _ _ houter hinner] at hscale'
  have hreverse := cyclic_substitution_fixed_point _ _ p hfixed
  obtain ⟨hconnectedForward, hcutForward, _⟩ := interior_fixed_point_geometry _ p hp hp' hfixed hscale
  obtain ⟨hconnectedBackward, hcutBackward, _⟩ := interior_fixed_point_geometry _ _ hpositive hless hreverse hscale'
  have hforward : (word initial middle * word suffix last).MassAdmissible :=
    ⟨hconnectedForward, hscale, hcutForward, houterSymmetric.mul hinnerSymmetric⟩
  have hbackward : (word suffix last * word initial middle).MassAdmissible :=
    ⟨hconnectedBackward, hscale', hcutBackward, hinnerSymmetric.mul houterSymmetric⟩
  rw [← (wordAppendEquivalence initial middle suffix last).massMatrix,
    ← (wordAppendEquivalence suffix last initial middle).massMatrix]
  exact cyclic_substitution_real_similarity _ _ houterSymmetric hinnerSymmetric hinner hforward hbackward p hp hp' hfixed

theorem cyclic_block_word_three_growth_values (initial suffix : List Rule) (middle last : Rule)
    (hinitial : ∀ rule ∈ initial, rule.TerminalSymmetric) (hmiddle : middle.TerminalSymmetric)
    (hsuffix : ∀ rule ∈ suffix, rule.TerminalSymmetric) (hlast : last.TerminalSymmetric)
    (p : ℝ) (hp : 0 < p) (hp' : p < 1)
    (hfixed : (word (initial ++ middle :: suffix) last).network.reliability p = p) :
    Real.log ((word (initial ++ middle :: suffix) last).edges : ℝ) / Real.log ((word (initial ++ middle :: suffix) last).network.fullGraph.dist (word (initial ++ middle :: suffix) last).network.source (word (initial ++ middle :: suffix) last).network.target) =
      Real.log ((word (suffix ++ last :: initial) middle).edges : ℝ) / Real.log ((word (suffix ++ last :: initial) middle).network.fullGraph.dist (word (suffix ++ last :: initial) middle).network.source (word (suffix ++ last :: initial) middle).network.target) ∧
    Real.log ((spectralRadius ℂ (((word (initial ++ middle :: suffix) last).network.massMatrix p).map Complex.ofReal)).toReal) / Real.log ((word (initial ++ middle :: suffix) last).network.fullGraph.dist (word (initial ++ middle :: suffix) last).network.source (word (initial ++ middle :: suffix) last).network.target) =
      Real.log ((spectralRadius ℂ (((word (suffix ++ last :: initial) middle).network.massMatrix ((word suffix last).network.reliability p)).map Complex.ofReal)).toReal) / Real.log ((word (suffix ++ last :: initial) middle).network.fullGraph.dist (word (suffix ++ last :: initial) middle).network.source (word (suffix ++ last :: initial) middle).network.target) ∧
    Real.log (deriv (word (initial ++ middle :: suffix) last).network.reliability p) / Real.log ((word (initial ++ middle :: suffix) last).network.fullGraph.dist (word (initial ++ middle :: suffix) last).network.source (word (initial ++ middle :: suffix) last).network.target) =
      Real.log (deriv (word (suffix ++ last :: initial) middle).network.reliability ((word suffix last).network.reliability p)) / Real.log ((word (suffix ++ last :: initial) middle).network.fullGraph.dist (word (suffix ++ last :: initial) middle).network.source (word (suffix ++ last :: initial) middle).network.target) := by
  have hedgeLog := congrArg (fun value : ℕ => Real.log (value : ℝ)) (cyclic_block_word_edges initial suffix middle last)
  rw [hedgeLog,
    cyclic_block_word_distance initial suffix middle last p hp hp' hfixed,
    cyclic_block_word_spectralRadius initial suffix middle last hinitial hmiddle hsuffix hlast p hp hp' hfixed,
    cyclic_block_word_response initial suffix middle last p hfixed]
  exact ⟨rfl, rfl, rfl⟩

end
end Universality.Rule
