import Universality.Percolation.SingleTerminalGenerationMean
import Universality.Percolation.BirthMomentUpper

namespace Universality.FiniteNetwork
noncomputable section
variable {vertices edges outerVertices outerEdges innerVertices innerEdges : ℕ}

/-- Sum of powers of the single-terminal child masses incident to the source. -/
def sourceIncidentChildPower (R : FiniteNetwork outerVertices outerEdges)
    (S : FiniteNetwork innerVertices innerEdges) (configuration : Fin outerEdges → Configuration innerEdges)
    (order : ℕ) : ℝ :=
  ∑ edge ∈ R.sourceIncidentEdges,
    (if (R.endpoint edge).1 = R.source then (S.internalSelectedMass true false (configuration edge) : ℝ)
      else S.internalSelectedMass false true (configuration edge)) ^ order

theorem sourceIncidentChildMass_eq_sum (R : FiniteNetwork outerVertices outerEdges)
    (S : FiniteNetwork innerVertices innerEdges) (configuration : Fin outerEdges → Configuration innerEdges) :
    (R.sourceIncidentChildMass S configuration : ℝ) =
      ∑ edge ∈ R.sourceIncidentEdges,
        if (R.endpoint edge).1 = R.source then (S.internalSelectedMass true false (configuration edge) : ℝ)
        else S.internalSelectedMass false true (configuration edge) := by
  simp only [sourceIncidentChildMass, Nat.cast_sum, Nat.cast_ite, Nat.cast_zero,
    sourceIncidentEdges, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro edge _
  by_cases hfirst : (R.endpoint edge).1 = R.source
  · simp [hfirst]
  · by_cases hsecond : (R.endpoint edge).2 = R.source <;> simp [hfirst, hsecond]

theorem sourceIncidentChildMass_pow_le (R : FiniteNetwork outerVertices outerEdges)
    (S : FiniteNetwork innerVertices innerEdges) (configuration : Fin outerEdges → Configuration innerEdges)
    (order : ℕ) (horder : 1 ≤ order) :
    (R.sourceIncidentChildMass S configuration : ℝ) ^ order ≤
      (R.sourceIncidentEdges.card : ℝ) ^ (order - 1) * R.sourceIncidentChildPower S configuration order := by
  rw [R.sourceIncidentChildMass_eq_sum S configuration]
  have holder := Real.rpow_sum_le_const_mul_sum_rpow_of_nonneg R.sourceIncidentEdges
    (f := fun edge => if (R.endpoint edge).1 = R.source then (S.internalSelectedMass true false (configuration edge) : ℝ)
      else S.internalSelectedMass false true (configuration edge)) (p := (order : ℝ))
    (by exact_mod_cast horder) (by intro edge _; split <;> exact Nat.cast_nonneg _)
  have hcast : (order : ℝ) - 1 = ((order - 1 : ℕ) : ℝ) := by
    rw [Nat.cast_sub horder, Nat.cast_one]
  rw [hcast] at holder
  simpa only [Real.rpow_natCast, sourceIncidentChildPower] using holder

theorem internalSelectedMass_substitute_pow_le_incident_add_crossings
    (R : FiniteNetwork outerVertices outerEdges) (S : FiniteNetwork innerVertices innerEdges)
    (configuration : Fin outerEdges → Configuration innerEdges) (order : ℕ) (horder : 1 ≤ order) :
    ((R.substitute S).internalSelectedMass true false (substitutionConfigurationEquiv configuration) : ℝ) ^ order ≤
      (R.sourceIncidentEdges.card : ℝ) ^ (order - 1) * R.sourceIncidentChildPower S configuration order +
        (Fintype.card (R.SubstitutionVertex S) : ℝ) ^ order *
          ∑ edge : Fin outerEdges, if S.crosses (configuration edge) then (1 : ℝ) else 0 := by
  have hpowerNonneg : 0 ≤ R.sourceIncidentChildPower S configuration order := by
    apply Finset.sum_nonneg
    intro edge _
    apply pow_nonneg
    split <;> exact Nat.cast_nonneg _
  by_cases hfail : ∀ edge, S.crosses (configuration edge) = false
  · rw [R.internalSelectedMass_substitute_all_child_failures S configuration hfail]
    exact (R.sourceIncidentChildMass_pow_le S configuration order horder).trans
      (le_add_of_nonneg_right (mul_nonneg (pow_nonneg (Nat.cast_nonneg _) _)
        (Finset.sum_nonneg (by intro edge _; split <;> norm_num))))
  · push Not at hfail
    obtain ⟨edge, hedge⟩ := hfail
    have hcross : S.crosses (configuration edge) = true := by
      cases hstate : S.crosses (configuration edge) <;> simp_all
    have hsum : 1 ≤ ∑ e : Fin outerEdges, if S.crosses (configuration e) then (1 : ℝ) else 0 := by
      have hs := Finset.single_le_sum (s := Finset.univ)
        (f := fun e : Fin outerEdges => if S.crosses (configuration e) then (1 : ℝ) else 0)
        (by intro e _; split <;> norm_num) (Finset.mem_univ edge)
      simpa only [hcross, ↓reduceIte] using hs
    have hbound : ((R.substitute S).internalSelectedMass true false (substitutionConfigurationEquiv configuration) : ℝ) ≤
        (Fintype.card (R.SubstitutionVertex S) : ℝ) := by
      have hb := (R.substitute S).internalSelectedMass_le true false (substitutionConfigurationEquiv configuration)
      have hc : Fintype.card (R.substitute S).InteriorVertex ≤ Fintype.card (R.SubstitutionVertex S) := by
        rw [(R.substitute S).card_interior_vertices]
        exact Nat.sub_le _ _
      exact_mod_cast hb.trans hc
    exact (pow_le_pow_left₀ (Nat.cast_nonneg _) hbound order).trans
      ((le_mul_of_one_le_right (pow_nonneg (Nat.cast_nonneg _) _) hsum).trans
        (le_add_of_nonneg_left (mul_nonneg (pow_nonneg (Nat.cast_nonneg _) _) hpowerNonneg)))

end
end Universality.FiniteNetwork
