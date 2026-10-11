import Universality.Percolation.PhysicalExponentClass
import Universality.Graph.ArbitraryCyclicWord

namespace Universality.Rule
noncomputable section
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
variable [MeasurableSpace Bool] [MeasurableSingletonClass Bool]
variable {first second : Rule}
variable [Nonempty first.network.InteriorVertex] [NeZero first.edges]
variable [Nonempty second.network.InteriorVertex] [NeZero second.edges]

theorem Classical.same_exponent_class_of_equal_growth_data
    (hfirst : first.Classical) (hsecond : second.Classical)
    (criticalFirst criticalSecond : ℝ)
    (hcFirst : 0 < criticalFirst) (hcFirst' : criticalFirst < 1)
    (hfixedFirst : first.network.reliability criticalFirst = criticalFirst)
    (hcSecond : 0 < criticalSecond) (hcSecond' : criticalSecond < 1)
    (hfixedSecond : second.network.reliability criticalSecond = criticalSecond)
    (hedges : first.edges = second.edges)
    (hdistance : first.network.fullGraph.dist first.network.source first.network.target =
      second.network.fullGraph.dist second.network.source second.network.target)
    (hmass : spectralRadius ℂ ((first.network.massMatrix criticalFirst).map Complex.ofReal) =
      spectralRadius ℂ ((second.network.massMatrix criticalSecond).map Complex.ofReal))
    (hresponse : deriv first.network.reliability criticalFirst = deriv second.network.reliability criticalSecond) :
    SameCriticalExponentUniversalityClass first second hfirst.edges_gt_one hsecond.edges_gt_one
      criticalFirst criticalSecond := by
  apply (hfirst.same_critical_exponent_class_iff_dimensions hsecond criticalFirst criticalSecond
    hcFirst hcFirst' hfixedFirst hcSecond hcSecond' hfixedSecond).mpr
  have hedgeLog := congrArg (fun n : ℕ => Real.log (n : ℝ)) hedges
  rw [hedgeLog, hdistance, hmass, hresponse]
  exact ⟨rfl, rfl, rfl⟩

variable (outer inner : Rule)
variable [Nonempty (outer * inner).network.InteriorVertex] [NeZero (outer * inner).edges]
variable [Nonempty (inner * outer).network.InteriorVertex] [NeZero (inner * outer).edges]

theorem cyclic_substitution_physical_exponent_class
    (houter : outer.TerminalSymmetric) (hinner : inner.TerminalSymmetric)
    (hforward : (outer * inner).Classical) (hbackward : (inner * outer).Classical)
    (p : ℝ) (hp : 0 < p) (hp' : p < 1)
    (hfixed : (outer * inner).network.reliability p = p) :
    SameCriticalExponentUniversalityClass (outer * inner) (inner * outer)
      hforward.edges_gt_one hbackward.edges_gt_one p (inner.network.reliability p) := by
  obtain ⟨hpositive, hless, hinnerConnected, houterConnected⟩ := cyclic_factor_interior outer inner p hp hp' hfixed
  obtain ⟨outerSymmetry, hos, hot⟩ := houter
  obtain ⟨innerSymmetry, his, hit⟩ := hinner
  apply hforward.same_exponent_class_of_equal_growth_data hbackward p (inner.network.reliability p)
    hp hp' hfixed hpositive hless (cyclic_substitution_fixed_point outer inner p hfixed)
  · simp only [mul_edges, Nat.mul_comm]
  · exact cyclic_substitution_distance outer inner houterConnected hinnerConnected
  · exact cyclic_substitution_spectralRadius outer inner p hp hp' hinnerConnected hfixed
      outerSymmetry hos hot innerSymmetry his hit
  · exact cyclic_substitution_response outer inner p hfixed

variable (initial suffix : List Rule) (middle last : Rule)
variable [Nonempty (word (initial ++ middle :: suffix) last).network.InteriorVertex] [NeZero (word (initial ++ middle :: suffix) last).edges]
variable [Nonempty (word (suffix ++ last :: initial) middle).network.InteriorVertex] [NeZero (word (suffix ++ last :: initial) middle).edges]

theorem cyclic_block_word_physical_exponent_class
    (hinitial : ∀ rule ∈ initial, rule.TerminalSymmetric) (hmiddle : middle.TerminalSymmetric)
    (hsuffix : ∀ rule ∈ suffix, rule.TerminalSymmetric) (hlast : last.TerminalSymmetric)
    (hforward : (word (initial ++ middle :: suffix) last).Classical) (hbackward : (word (suffix ++ last :: initial) middle).Classical)
    (p : ℝ) (hp : 0 < p) (hp' : p < 1)
    (hfixed : (word (initial ++ middle :: suffix) last).network.reliability p = p) :
    SameCriticalExponentUniversalityClass (word (initial ++ middle :: suffix) last) (word (suffix ++ last :: initial) middle)
      hforward.edges_gt_one hbackward.edges_gt_one p ((word suffix last).network.reliability p) := by
  have hfactor := hfixed
  rw [← (wordAppendEquivalence initial middle suffix last).reliability] at hfactor
  obtain ⟨hpositive, hless, _, _⟩ := cyclic_factor_interior (word initial middle) (word suffix last) p hp hp' hfactor
  apply (hforward.same_critical_exponent_class_iff_dimensions hbackward p ((word suffix last).network.reliability p)
    hp hp' hfixed hpositive hless (cyclic_block_word_fixed_point initial suffix middle last p hfixed)).mpr
  exact cyclic_block_word_three_growth_values initial suffix middle last hinitial hmiddle hsuffix hlast p hp hp' hfixed

end
end Universality.Rule
