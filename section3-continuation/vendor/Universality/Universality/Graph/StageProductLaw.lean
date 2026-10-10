import Universality.Graph.OriginCoordinate
import Mathlib.Probability.Independence.InfinitePi

namespace Universality.NetworkTower
noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory ProbabilityTheory
variable [MeasurableSpace Bool]

/-- Independent raw coordinates on every indexed finite-stage edge. Coordinates
already inherited from an earlier stage are ignored by the configuration map. -/
def rawEdgeLaw (tower : NetworkTower) (law : Measure Bool) [IsProbabilityMeasure law] :
    Measure ((Σ n, Fin (tower.stage n).edges) → Bool) :=
  Measure.infinitePi (fun _ : Σ n, Fin (tower.stage n).edges => law)

instance rawEdgeLaw_probability (tower : NetworkTower) (law : Measure Bool)
    [IsProbabilityMeasure law] : IsProbabilityMeasure (tower.rawEdgeLaw law) := by
  unfold rawEdgeLaw
  infer_instance

def sampledConfiguration (tower : NetworkTower)
    (bits : (Σ n, Fin (tower.stage n).edges) → Bool) : tower.Edge → Bool :=
  tower.configuration (fun n e => bits ⟨n, e⟩)

/-- The actual configuration in each embedded finite cell has the full product
law. This follows from injective selection of independently sampled coordinates. -/
theorem stageConfiguration_measurePreserving (tower : NetworkTower)
    (law : Measure Bool) [IsProbabilityMeasure law] (n : ℕ) :
    MeasurePreserving
      (fun bits : (Σ k, Fin (tower.stage k).edges) → Bool =>
        tower.stageConfiguration (fun k e => bits ⟨k, e⟩) n)
      (tower.rawEdgeLaw law) (Measure.pi (fun _ : Fin (tower.stage n).edges => law)) := by
  have heq : (fun bits : (Σ k, Fin (tower.stage k).edges) → Bool =>
      tower.stageConfiguration (fun k e => bits ⟨k, e⟩) n) =
      (fun bits => fun e => bits (tower.originEmbedding n e)) := by
    funext bits e
    exact tower.stageConfiguration_eq_origin (fun k edge => bits ⟨k, edge⟩) n e
  rw [heq]
  refine ⟨measurable_pi_lambda _ (fun e => measurable_pi_apply (tower.originEmbedding n e)), ?_⟩
  unfold rawEdgeLaw
  rw [Measure.map_infinitePi_infinitePi_of_inj (tower.originEmbedding n).injective,
    Measure.infinitePi_eq_pi]

theorem sampledConfiguration_restrict_measurePreserving (tower : NetworkTower)
    (law : Measure Bool) [IsProbabilityMeasure law] (n : ℕ) :
    MeasurePreserving
      (fun bits => tower.restrictConfiguration (tower.sampledConfiguration bits) n)
      (tower.rawEdgeLaw law) (Measure.pi (fun _ : Fin (tower.stage n).edges => law)) := by
  simpa only [sampledConfiguration, restrict_configuration] using
    tower.stageConfiguration_measurePreserving law n

end
end Universality.NetworkTower
