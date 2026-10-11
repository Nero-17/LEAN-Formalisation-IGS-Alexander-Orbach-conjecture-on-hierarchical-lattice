import Universality.Percolation.BirthSeriesScaling

namespace Universality
noncomputable section

theorem discounted_postexit_power_identity (edges growth decay coefficient : ℝ)
    (hedges : 0 < edges) (order offset depth : ℕ) :
    (1 / edges) ^ (offset + depth + 2) *
        (coefficient * growth ^ (order * offset) * decay ^ depth) =
      (coefficient / edges ^ 2) * (growth ^ order / edges) ^ offset * (decay / edges) ^ depth := by
  simp only [div_pow, one_pow, pow_add, pow_mul]
  field_simp [hedges.ne']
  <;> ring

end
end Universality
