import Universality.Percolation.FiniteCharacteristicPropagation
import Universality.Percolation.FiniteCharacteristicSpan
import Universality.Percolation.DisconnectedMassSpan
import Universality.Percolation.AllTypesMassNonlattice

namespace Universality.Rule
noncomputable section
open FiniteNetwork

/-- At the second substitution depth every conditional mass is aperiodic.
Only the elementary zero/one support for the two noncrossing types is needed;
positive-probability offspring configurations transfer strictness to the connected type. -/
theorem Classical.internal_mass_base_characteristic_strict {rule : Rule} (h : rule.Classical)
    (p : ℝ) (hp : 0 < p) (hp' : p < 1) (hfixed : rule.network.reliability p = p)
    (t : ℝ) (ht : Complex.exp ((t : ℂ) * Complex.I) ≠ 1) (state : LiveState) :
    ‖(rule.generation 1).network.conditionalVertexCharacteristic p state t‖ < 1 := by
  have hbase (targetSelected : Bool) :
      ‖rule.network.conditionalInternalCharacteristic p false true targetSelected t‖ < 1 := by
    obtain ⟨first, second, hfirst, hsecond, hmassFirst, hmassSecond⟩ :=
      rule.network.disconnected_mass_consecutive_configurations p hp hp' hfixed (h.connected _) h.scale targetSelected
    exact rule.network.conditional_mass_norm_lt_one_of_zero_one p hp.le hp'.le
      (by rwa [hfixed]) (by rwa [hfixed]) false true targetSelected first second
      hfirst hsecond hmassFirst hmassSecond t ht
  have hnorm : ‖(rule.generation 1).network.conditionalVertexCharacteristic p state t‖ ≤ 1 :=
    (rule.generation 1).network.norm_conditionalInternalCharacteristic_le_one p hp.le hp'.le
      (by rwa [rule.generation_fixed_point p hfixed 1]) (by rwa [rule.generation_fixed_point p hfixed 1]) _ _ _ _
  by_contra hnot
  have hunit := le_antisymm hnorm (le_of_not_gt hnot)
  cases state with
  | connected =>
    obtain ⟨edge, hchild⟩ := rule.network.exists_closed_edge_both_endpoints_active (h.connected _) h.cut
    have hpositive : 0 < rule.network.conditionalCellWeight p true (onlyClosed edge) := by
      simp only [conditionalCellWeight, h.cut edge, ↓reduceIte, hfixed]
      exact div_pos (bernoulliWeight_pos hp hp' _) hp
    have hchildUnit := rule.generation_child_characteristic_unit h.massAdmissible.symmetric p hp hp' hfixed
      0 t .connected .both (onlyClosed edge) edge hpositive hchild hunit
    exact (hbase true).ne hchildUnit
  | both =>
    obtain ⟨edge, hincident⟩ := rule.network.exists_source_incident_edge (h.connected _)
    obtain ⟨hfirst, hsecond⟩ := rule.network.incident_endpoints_ne_target edge hincident h.scale
    have hchildUnit := rule.generation_child_characteristic_unit h.massAdmissible.symmetric p hp hp' hfixed
      0 t .both .single (fun _ => false) edge
      (rule.network.conditionalCellWeight_allClosed_pos p hp hp' hfixed)
      (rule.network.childState_allClosed_both_single edge hincident hfirst hsecond) hunit
    exact (hbase false).ne hchildUnit
  | single =>
    obtain ⟨edge, hincident⟩ := rule.network.exists_source_incident_edge (h.connected _)
    have hchildUnit := rule.generation_child_characteristic_unit h.massAdmissible.symmetric p hp hp' hfixed
      0 t .single .single (fun _ => false) edge
      (rule.network.conditionalCellWeight_allClosed_pos p hp hp' hfixed)
      (rule.network.childState_allClosed_single edge hincident) hunit
    exact (hbase false).ne hchildUnit

end
end Universality.Rule

