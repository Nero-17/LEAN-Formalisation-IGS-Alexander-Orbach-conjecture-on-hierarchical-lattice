import Universality.Analysis.TaylorResponseExponent

namespace Universality
noncomputable section
open Filter
open scoped Topology

theorem contDiffAt_iteratedDeriv_of_add (density : ℝ → ℝ) (critical : ℝ)
    (order number : ℕ) (hregular : ContDiffAt ℝ (order + number : ℕ) density critical) :
    ContDiffAt ℝ order (iteratedDeriv number density) critical := by
  induction number generalizing density with
  | zero => simpa using hregular
  | succ number ih =>
    rw [iteratedDeriv_succ']
    apply ih
    exact hregular.derivWithin (by simp only [Nat.cast_add, Nat.cast_succ, add_assoc, le_refl])

theorem iteratedDeriv_add_apply_real (density : ℝ → ℝ) (first second : ℕ) (p : ℝ) :
    iteratedDeriv first (iteratedDeriv second density) p =
      iteratedDeriv (first + second) density p := by
  simp only [iteratedDeriv_eq_iterate, Function.iterate_add_apply]

/-- The exact finite-regularity implication in the manuscript's cluster-number
response proposition. Applying it to the physical density still requires the
separate theorem establishing its stated local regularity. -/
theorem raw_cluster_number_alpha_criterion (density : ℝ → ℝ) (critical : ℝ) (j : ℕ)
    (hj : 3 ≤ j) (hregular : ContDiffAt ℝ j density critical)
    (hvanish : ∀ i, 3 ≤ i → i < j → iteratedDeriv i density critical = 0)
    (hleading : iteratedDeriv j density critical ≠ 0) :
    ((∀ᶠ p in 𝓝[<] critical, iteratedDeriv 3 density p ≠ 0) ∧
      Tendsto (fun p => -1 - Real.log |iteratedDeriv 3 density p| /
        Real.log |p - critical|) (𝓝[<] critical) (𝓝 (2 - (j : ℝ)))) ∧
    ((∀ᶠ p in 𝓝[>] critical, iteratedDeriv 3 density p ≠ 0) ∧
      Tendsto (fun p => -1 - Real.log |iteratedDeriv 3 density p| /
        Real.log |p - critical|) (𝓝[>] critical) (𝓝 (2 - (j : ℝ)))) := by
  have horder : j - 3 + 3 = j := Nat.sub_add_cancel hj
  have hresponse : ContDiffAt ℝ (j - 3 : ℕ) (iteratedDeriv 3 density) critical :=
    contDiffAt_iteratedDeriv_of_add density critical (j - 3) 3 (by simpa [horder] using hregular)
  have hzero (i : ℕ) (hi : i < j - 3) :
      iteratedDeriv i (iteratedDeriv 3 density) critical = 0 := by
    rw [iteratedDeriv_add_apply_real]
    exact hvanish (i + 3) (by omega) (by omega)
  have hnonzero : iteratedDeriv (j - 3) (iteratedDeriv 3 density) critical ≠ 0 := by
    rw [iteratedDeriv_add_apply_real, horder]
    exact hleading
  obtain ⟨hleft, hright⟩ := two_sided_logarithmic_order_of_first_derivative
    (iteratedDeriv 3 density) critical (j - 3) hresponse hzero hnonzero
  have hvalue : -1 - ((j - 3 : ℕ) : ℝ) = 2 - (j : ℝ) := by
    rw [Nat.cast_sub hj]
    norm_num
    ring
  exact ⟨⟨hleft.1, by simpa only [hvalue] using hleft.2.const_sub (-1)⟩,
    ⟨hright.1, by simpa only [hvalue] using hright.2.const_sub (-1)⟩⟩

end
end Universality
