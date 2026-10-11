import Universality.Percolation.PhysicalExponentDimensions

namespace Universality.Rule
noncomputable section
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
variable [MeasurableSpace Bool] [MeasurableSingletonClass Bool]

def SameCriticalExponentUniversalityClass (first second : Rule)
    [Nonempty first.network.InteriorVertex] [NeZero first.edges]
    [Nonempty second.network.InteriorVertex] [NeZero second.edges]
    (hfirst : 1 < first.edges) (hsecond : 1 < second.edges)
    (criticalFirst criticalSecond : ℝ) : Prop :=
  ∃ beta nu delta eta : ℝ,
    first.HasCriticalExponents hfirst criticalFirst beta nu delta eta ∧
    second.HasCriticalExponents hsecond criticalSecond beta nu delta eta

variable {first second : Rule}
variable [Nonempty first.network.InteriorVertex] [NeZero first.edges]
variable [Nonempty second.network.InteriorVertex] [NeZero second.edges]

theorem Classical.same_critical_exponent_class_iff_dimensions
    (hfirst : first.Classical) (hsecond : second.Classical)
    (criticalFirst criticalSecond : ℝ)
    (hcFirst : 0 < criticalFirst) (hcFirst' : criticalFirst < 1)
    (hfixedFirst : first.network.reliability criticalFirst = criticalFirst)
    (hcSecond : 0 < criticalSecond) (hcSecond' : criticalSecond < 1)
    (hfixedSecond : second.network.reliability criticalSecond = criticalSecond) :
    SameCriticalExponentUniversalityClass first second hfirst.edges_gt_one hsecond.edges_gt_one
      criticalFirst criticalSecond ↔
      (Real.log (first.edges : ℝ) / (Real.log (first.network.fullGraph.dist first.network.source first.network.target : ℝ))) = (Real.log (second.edges : ℝ) / (Real.log (second.network.fullGraph.dist second.network.source second.network.target : ℝ))) ∧
      (Real.log ((spectralRadius ℂ ((first.network.massMatrix criticalFirst).map Complex.ofReal)).toReal) / (Real.log (first.network.fullGraph.dist first.network.source first.network.target : ℝ))) = (Real.log ((spectralRadius ℂ ((second.network.massMatrix criticalSecond).map Complex.ofReal)).toReal) / (Real.log (second.network.fullGraph.dist second.network.source second.network.target : ℝ))) ∧
      (Real.log (deriv first.network.reliability criticalFirst) / (Real.log (first.network.fullGraph.dist first.network.source first.network.target : ℝ))) = (Real.log (deriv second.network.reliability criticalSecond) / (Real.log (second.network.fullGraph.dist second.network.source second.network.target : ℝ))) := by
  have hformulas := four_exponent_formulas_eq_iff_dimensions_eq
    (Real.log (first.edges : ℝ) / (Real.log (first.network.fullGraph.dist first.network.source first.network.target : ℝ)))
    (Real.log ((spectralRadius ℂ ((first.network.massMatrix criticalFirst).map Complex.ofReal)).toReal) / (Real.log (first.network.fullGraph.dist first.network.source first.network.target : ℝ)))
    (Real.log (deriv first.network.reliability criticalFirst) / (Real.log (first.network.fullGraph.dist first.network.source first.network.target : ℝ)))
    (Real.log (second.edges : ℝ) / (Real.log (second.network.fullGraph.dist second.network.source second.network.target : ℝ)))
    (Real.log ((spectralRadius ℂ ((second.network.massMatrix criticalSecond).map Complex.ofReal)).toReal) / (Real.log (second.network.fullGraph.dist second.network.source second.network.target : ℝ)))
    (Real.log (deriv second.network.reliability criticalSecond) / (Real.log (second.network.fullGraph.dist second.network.source second.network.target : ℝ)))
    (hfirst.critical_dimension_gap_positive criticalFirst hcFirst hcFirst').ne'
    (hsecond.critical_dimension_gap_positive criticalSecond hcSecond hcSecond').ne'
    (hfirst.pivotal_mass_inequalities criticalFirst hcFirst hcFirst' hfixedFirst).1.ne'
    (hsecond.pivotal_mass_inequalities criticalSecond hcSecond hcSecond' hfixedSecond).1.ne'
  have hfirstExponents := hfirst.hasCriticalExponents_in_dimensions criticalFirst hcFirst hcFirst' hfixedFirst
  have hsecondExponents := hsecond.hasCriticalExponents_in_dimensions criticalSecond hcSecond hcSecond' hfixedSecond
  constructor
  · rintro ⟨beta, nu, delta, eta, hfirstActual, hsecondActual⟩
    have hfirstValues := critical_exponents_unique hfirst.edges_gt_one criticalFirst
      _ _ _ _ _ _ _ _ hfirstActual hfirstExponents
    have hsecondValues := critical_exponents_unique hsecond.edges_gt_one criticalSecond
      _ _ _ _ _ _ _ _ hsecondActual hsecondExponents
    exact hformulas.mp ⟨hfirstValues.1.symm.trans hsecondValues.1,
      hfirstValues.2.1.symm.trans hsecondValues.2.1,
      hfirstValues.2.2.1.symm.trans hsecondValues.2.2.1,
      hfirstValues.2.2.2.symm.trans hsecondValues.2.2.2⟩
  · intro hdimensions
    obtain ⟨hbeta, hnu, hdelta, heta⟩ := hformulas.mpr hdimensions
    refine ⟨_, _, _, _, hfirstExponents, ?_⟩
    rw [hbeta, hnu, hdelta, heta]
    exact hsecondExponents

end
end Universality.Rule
