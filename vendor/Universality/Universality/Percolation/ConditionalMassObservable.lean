import Universality.Percolation.ConditionalMassInversion
import Universality.Percolation.GenerationMassCharacteristic

namespace Universality.FiniteNetwork
noncomputable section

def conditionalInternalMassObservable {vertices edges : ℕ} (R : FiniteNetwork vertices edges)
    (p : ℝ) (opened sourceSelected targetSelected : Bool) (response : ℕ → ℝ) : ℝ :=
  ∑ configuration, R.conditionalCellWeight p opened configuration *
    response (R.internalSelectedMass sourceSelected targetSelected configuration)

theorem conditionalInternalMassObservable_atom {vertices edges : ℕ} (R : FiniteNetwork vertices edges)
    (p : ℝ) (opened sourceSelected targetSelected : Bool) (size : ℕ) :
    R.conditionalInternalMassObservable p opened sourceSelected targetSelected (fun mass => if mass = size then 1 else 0) =
      R.conditionalInternalMassProbability p opened sourceSelected targetSelected size := by
  simp only [conditionalInternalMassObservable, conditionalInternalMassProbability, mul_ite, mul_one, mul_zero]

theorem conditionalInternalMassObservable_power {vertices edges : ℕ} (R : FiniteNetwork vertices edges)
    (p : ℝ) (opened sourceSelected targetSelected : Bool) (order : ℕ) :
    R.conditionalInternalMassObservable p opened sourceSelected targetSelected (fun mass => (mass : ℝ) ^ order) =
      R.conditionalInternalMoment p opened sourceSelected targetSelected order := rfl

theorem conditionalInternalMassObservable_substitute {outerVertices outerEdges innerVertices innerEdges : ℕ}
    (R : FiniteNetwork outerVertices outerEdges) (S : FiniteNetwork innerVertices innerEdges)
    (p : ℝ) (hpositive : 0 < S.reliability p) (hless : S.reliability p < 1)
    (opened sourceSelected targetSelected : Bool) (response : ℕ → ℝ) :
    (R.substitute S).conditionalInternalMassObservable p opened sourceSelected targetSelected response =
      ∑ coarse, R.conditionalCellWeight (S.reliability p) opened coarse *
        ∑ cells : Fin outerEdges → Configuration innerEdges,
          (∏ e, S.conditionalCellWeight p (coarse e) (cells e)) *
            response (R.internalSelectedMass sourceSelected targetSelected coarse +
              ∑ e, S.internalStateMass (R.orientedChildState sourceSelected targetSelected coarse e) (cells e)) := by
  unfold conditionalInternalMassObservable
  rw [← substitutionConfigurationEquiv.sum_comp]
  simp_rw [R.internalSelectedMass_substitute S]
  exact R.conditional_substitution_observable S p hpositive hless opened
    (fun coarse cells => response (R.internalSelectedMass sourceSelected targetSelected coarse +
      ∑ e, S.internalStateMass (R.orientedChildState sourceSelected targetSelected coarse e) (cells e)))

end
end Universality.FiniteNetwork

namespace Universality.FiniteNetwork.NetworkEquivalence
noncomputable section

theorem conditionalInternalMassObservable {vR eR vS eS : ℕ} {R : FiniteNetwork vR eR} {S : FiniteNetwork vS eS}
    (equivalence : R.NetworkEquivalence S) (p : ℝ) (opened sourceSelected targetSelected : Bool) (response : ℕ → ℝ) :
    S.conditionalInternalMassObservable p opened sourceSelected targetSelected response =
      R.conditionalInternalMassObservable p opened sourceSelected targetSelected response := by
  unfold FiniteNetwork.conditionalInternalMassObservable
  rw [← equivalence.configuration.sum_comp]
  simp only [equivalence.conditionalCellWeight, equivalence.internalSelectedMass]

end
end Universality.FiniteNetwork.NetworkEquivalence

namespace Universality.Rule
noncomputable section
open FiniteNetwork

theorem generation_conditionalInternalMassObservable (rule : Rule)
    (p : ℝ) (hp : 0 < p) (hp' : p < 1) (hfixed : rule.network.reliability p = p)
    (n : ℕ) (opened sourceSelected targetSelected : Bool) (response : ℕ → ℝ) :
    (rule.generation (n + 1)).network.conditionalInternalMassObservable p opened sourceSelected targetSelected response =
      ∑ coarse, rule.network.conditionalCellWeight p opened coarse *
        ∑ cells : Fin rule.edges → Configuration (rule.generation n).edges,
          (∏ e, (rule.generation n).network.conditionalCellWeight p (coarse e) (cells e)) *
            response (rule.network.internalSelectedMass sourceSelected targetSelected coarse +
              ∑ e, (rule.generation n).network.internalStateMass
                (rule.network.orientedChildState sourceSelected targetSelected coarse e) (cells e)) := by
  rw [← (rule.generationTopDecomposition n).conditionalInternalMassObservable]
  rw [rule.network.conditionalInternalMassObservable_substitute (rule.generation n).network p
    (by rwa [rule.generation_fixed_point p hfixed n]) (by rwa [rule.generation_fixed_point p hfixed n]),
    rule.generation_fixed_point p hfixed n]

end
end Universality.Rule
