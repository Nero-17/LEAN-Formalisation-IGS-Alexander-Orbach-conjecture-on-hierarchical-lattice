import Universality.Arithmetic.GraphCriticalDimensions
import Universality.Graph.ClassicalSubstitution

/-!
# Iteration and alignment of actual classical graph rules

`generation n` is the result of `n + 1` substitutions in the existing graph
API.  The final theorems also use positive substitution counts explicitly.
-/

namespace Universality.Rule
noncomputable section
open FiniteNetwork Matrix

theorem Classical.generation_interior_fixed_point_iff {rule : Rule}
    (h : rule.Classical) (n : ℕ) (p : ℝ) (hp : 0 < p) (hp' : p < 1) :
    (rule.generation n).network.reliability p = p ↔ rule.network.reliability p = p := by
  constructor
  · intro hfixed
    obtain ⟨critical, hcritical, hcritical', hfixedCritical⟩ := h.exists_interior_fixed_point
    have hequal := (rule.generation n).network.interior_fixed_point_unique p critical
      hp hp' hcritical hcritical' hfixed
      (rule.generation_fixed_point critical hfixedCritical n) (h.generation n).scale
    simpa only [hequal] using hfixedCritical
  · intro hfixed
    exact rule.generation_fixed_point p hfixed n

theorem Classical.generation_spectralRadius {rule : Rule} (h : rule.Classical)
    (p : ℝ) (hp : 0 < p) (hp' : p < 1)
    (hfixed : rule.network.reliability p = p) (n : ℕ) :
    (spectralRadius ℂ
      (((rule.generation n).network.massMatrix p).map Complex.ofReal)).toReal =
      (spectralRadius ℂ ((rule.network.massMatrix p).map Complex.ofReal)).toReal ^ (n + 1) := by
  obtain ⟨symmetry, hsource, htarget⟩ := h.massAdmissible.symmetric
  rw [rule.generation_massMatrix p hfixed hp hp' symmetry hsource htarget n]
  obtain ⟨hpositive, weight, hweight, heigenvector⟩ :=
    h.mass_spectralRadius_positive_eigenvector p hp hp'
  rw [spectralRadius_eq_of_positive_eigenvector
    (rule.network.massMatrix p ^ (n + 1)) weight
    ((spectralRadius ℂ ((rule.network.massMatrix p).map Complex.ofReal)).toReal ^ (n + 1))
    (matrix_pow_nonneg _ (rule.network.massMatrix_nonneg hp.le hp'.le) _)
    hweight (pow_nonneg hpositive.le _)
    (common_eigenvector_pow _ weight _ heigenvector (n + 1)),
    ENNReal.toReal_ofReal (pow_nonneg hpositive.le _)]

/-- Every response in Proposition `iterated-response` is computed on the actual
iterated finite graph. -/
theorem Classical.iterated_responses {rule : Rule} (h : rule.Classical)
    (p : ℝ) (hp : 0 < p) (hp' : p < 1)
    (hfixed : rule.network.reliability p = p) (steps : ℕ) (hsteps : 0 < steps) :
    (rule.generation (steps - 1)).Classical ∧
    (rule.generation (steps - 1)).network.reliability p = p ∧
    (rule.generation (steps - 1)).edges = rule.edges ^ steps ∧
    (rule.generation (steps - 1)).network.fullGraph.dist
      (rule.generation (steps - 1)).network.source
      (rule.generation (steps - 1)).network.target =
        rule.network.fullGraph.dist rule.network.source rule.network.target ^ steps ∧
    deriv (rule.generation (steps - 1)).network.reliability p =
      deriv rule.network.reliability p ^ steps ∧
    (rule.generation (steps - 1)).network.massMatrix p = rule.network.massMatrix p ^ steps ∧
    (spectralRadius ℂ
      (((rule.generation (steps - 1)).network.massMatrix p).map Complex.ofReal)).toReal =
      (spectralRadius ℂ ((rule.network.massMatrix p).map Complex.ofReal)).toReal ^ steps := by
  have hindex : steps - 1 + 1 = steps := Nat.sub_add_cancel hsteps
  obtain ⟨symmetry, hsource, htarget⟩ := h.massAdmissible.symmetric
  refine ⟨h.generation _, rule.generation_fixed_point p hfixed _, ?_, ?_, ?_, ?_, ?_⟩
  · simpa only [hindex] using rule.generation_edges (steps - 1)
  · simpa only [hindex] using rule.generation_terminal_distance (h.connected _) (steps - 1)
  · simpa only [hindex] using (rule.generation_hasDerivAt p hfixed (steps - 1)).deriv
  · simpa only [hindex] using rule.generation_massMatrix p hfixed hp hp'
      symmetry hsource htarget (steps - 1)
  · simpa only [hindex] using h.generation_spectralRadius p hp hp' hfixed (steps - 1)

theorem Classical.generation_criticalDimensions {rule : Rule} (h : rule.Classical)
    (p : ℝ) (hp : 0 < p) (hp' : p < 1)
    (hfixed : rule.network.reliability p = p) (n : ℕ) :
    (rule.generation n).criticalDimensions p = rule.criticalDimensions p := by
  funext index
  fin_cases index
  · exact rule.finite_edge_growth_formula (h.connected _) n
  · change Real.log _ / Real.log _ = Real.log _ / Real.log _
    rw [rule.generation_terminal_distance (h.connected _), Nat.cast_pow,
      h.generation_spectralRadius p hp hp' hfixed]
    exact Section4.normalized_log_pow _ _ _ (Nat.succ_pos n)
  · change Real.log _ / Real.log _ = Real.log _ / Real.log _
    rw [rule.generation_terminal_distance (h.connected _), Nat.cast_pow,
      (rule.generation_hasDerivAt p hfixed n).deriv]
    exact Section4.normalized_log_pow _ _ _ (Nat.succ_pos n)

/-- On aligned scales, equality of the actual three critical growth dimensions
is equivalent to equality of the three powered response multipliers. -/
theorem Classical.aligned_criticalDimensions_iff {first second : Rule}
    (hfirst : first.Classical) (hsecond : second.Classical)
    (p q : ℝ) (hp : 0 < p) (hp' : p < 1) (hq : 0 < q) (hq' : q < 1)
    (hfixedFirst : first.network.reliability p = p)
    (hfixedSecond : second.network.reliability q = q)
    (firstSteps secondSteps : ℕ) (hfirstSteps : 0 < firstSteps) (hsecondSteps : 0 < secondSteps)
    (haligned : first.network.fullGraph.dist first.network.source first.network.target ^ firstSteps =
      second.network.fullGraph.dist second.network.source second.network.target ^ secondSteps) :
    first.criticalDimensions p = second.criticalDimensions q ↔
      first.edges ^ firstSteps = second.edges ^ secondSteps ∧
      (spectralRadius ℂ ((first.network.massMatrix p).map Complex.ofReal)).toReal ^ firstSteps =
        (spectralRadius ℂ ((second.network.massMatrix q).map Complex.ofReal)).toReal ^ secondSteps ∧
      deriv first.network.reliability p ^ firstSteps =
        deriv second.network.reliability q ^ secondSteps := by
  have halignedReal :
      (first.network.fullGraph.dist first.network.source first.network.target : ℝ) ^ firstSteps =
        (second.network.fullGraph.dist second.network.source second.network.target : ℝ) ^ secondSteps := by
    exact_mod_cast haligned
  have hcompare (firstMultiplier secondMultiplier : ℝ)
      (hpositiveFirst : 0 < firstMultiplier) (hpositiveSecond : 0 < secondMultiplier) :=
    Section4.aligned_log_dimensions_iff
      (first.network.fullGraph.dist first.network.source first.network.target)
      (second.network.fullGraph.dist second.network.source second.network.target)
      firstMultiplier secondMultiplier firstSteps secondSteps
      (by exact_mod_cast hsecond.scale) hpositiveFirst hpositiveSecond
      hfirstSteps hsecondSteps halignedReal
  have hambient : first.criticalDimensions p 0 = second.criticalDimensions q 0 ↔
      first.edges ^ firstSteps = second.edges ^ secondSteps := by
    change Real.log _ / Real.log _ = Real.log _ / Real.log _ ↔ _
    rw [hcompare _ _ (by exact_mod_cast hfirst.edges_pos) (by exact_mod_cast hsecond.edges_pos)]
    exact_mod_cast (Iff.rfl : first.edges ^ firstSteps = second.edges ^ secondSteps ↔
      first.edges ^ firstSteps = second.edges ^ secondSteps)
  have hmass := hcompare _ _ (hfirst.mass_spectralRadius_positive_eigenvector p hp hp').1
    (hsecond.mass_spectralRadius_positive_eigenvector q hq hq').1
  have hpivotal := hcompare _ _
    (first.interior_fixed_point_spectral_dominance p hp hp' hfixedFirst
      hfirst.massAdmissible.symmetric hfirst.scale).1
    (second.interior_fixed_point_spectral_dominance q hq hq' hfixedSecond
      hsecond.massAdmissible.symmetric hsecond.scale).1
  constructor
  · intro hequal
    exact ⟨hambient.mp (congrFun hequal 0), hmass.mp (congrFun hequal 1),
      hpivotal.mp (congrFun hequal 2)⟩
  · rintro ⟨hedges, hmassEqual, hpivotalEqual⟩
    funext index
    fin_cases index
    · exact hambient.mpr hedges
    · exact hmass.mpr hmassEqual
    · exact hpivotal.mpr hpivotalEqual

end
end Universality.Rule

#print axioms Universality.Rule.Classical.generation_interior_fixed_point_iff
#print axioms Universality.Rule.Classical.iterated_responses
#print axioms Universality.Rule.Classical.generation_criticalDimensions
#print axioms Universality.Rule.Classical.aligned_criticalDimensions_iff
