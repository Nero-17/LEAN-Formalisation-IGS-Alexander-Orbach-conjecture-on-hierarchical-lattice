import IGSIII34.Spectral.Collars.ActualFiniteOriginalJointResponseTransport

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace IGSIII34.Spectral
noncomputable section
open Universality Universality.FiniteNetwork IGSIII.Geometry IGSIII.Chemical.Substitution
open IGSIII34.Diffusion IGSIII34.ResistanceLimit MeasureTheory

theorem actualFullConfigurationPathLaw_eq_placed
    (rule : Rule) (configuration : ∀ depth, Configuration (rule.generation depth).edges)
    (scale : ℝ) (scalePositive : 0 < scale) (depth : ℕ)
    (crossing : (rule.generation depth).network.crosses (configuration depth) = true)
    (initial : Fin (rule.generation depth).vertices)
    (clock : ℝ) (clockPositive : 0 < clock) (kind : Fin 3) :
    actualFullConfigurationPathLaw rule configuration scale scalePositive depth crossing initial
      clock clockPositive kind =
    actualFiniteAnnealedPlacedPathLaw rule scale scalePositive depth (configuration depth)
      crossing initial clock clockPositive kind
      (actualAnnealedFiniteVertexEquiv rule configuration scale scalePositive depth) :=
  (actualFiniteAnnealedPlacedPathLaw_eq_canonical_map rule scale scalePositive depth
    (configuration depth) crossing initial clock clockPositive kind
    (actualAnnealedFiniteVertexEquiv rule configuration scale scalePositive depth)
    (actualAnnealedFiniteVertexEquiv rule configuration scale scalePositive depth).continuous).symm

/-- Literal original discrete walk law, retaining every finite label and
its original normalized chemical distance. -/
theorem actualFullConfigurationPathLaw_discrete
    (rule : Rule) (configuration : ∀ depth, Configuration (rule.generation depth).edges)
    (scale : ℝ) (scalePositive : 0 < scale) (depth : ℕ)
    (crossing : (rule.generation depth).network.crosses (configuration depth) = true)
    (initial : ActualFiniteCluster rule configuration scale scalePositive depth)
    (clock : ℝ) (clockPositive : 0 < clock) :
    actualFullConfigurationPathLaw rule configuration scale scalePositive depth crossing initial.val
      clock clockPositive 0 =
    discreteCadlagProbabilityCompletion
      (Vertex := ActualFiniteCluster rule configuration scale scalePositive depth)
      (⟨finiteDiscreteWalkLaw
        (Vertex := ActualFiniteCluster rule configuration scale scalePositive depth)
        (clusterRetainedEndpoint (rule.generation depth).network (configuration depth))
        (cluster_degree_positive (rule.generation depth).network (configuration depth) crossing)
        (Measure.dirac initial), inferInstance⟩ : ProbabilityMeasure _)
      clock clockPositive id := by
  rw [actualFullConfigurationPathLaw_eq_placed]
  exact actualFiniteAnnealedPlacedPathLaw_discrete_configuration_transport
    rule configuration scale scalePositive depth crossing initial clock clockPositive id

/-- Literal original exponential holding walk law, including rate one
and rate one along every incident edge, at the prescribed clock. -/
theorem actualFullConfigurationPathLaw_weighted
    (rule : Rule) (configuration : ∀ depth, Configuration (rule.generation depth).edges)
    (scale : ℝ) (scalePositive : 0 < scale) (depth : ℕ)
    (crossing : (rule.generation depth).network.crosses (configuration depth) = true)
    (initial : ActualFiniteCluster rule configuration scale scalePositive depth)
    (clock : ℝ) (clockPositive : 0 < clock) (kind : Fin 3) (notDiscrete : kind ≠ 0) :
    actualFullConfigurationPathLaw rule configuration scale scalePositive depth crossing initial.val
      clock clockPositive kind =
    finiteWeightedCadlagProbabilityCompletion
      (Vertex := ActualFiniteCluster rule configuration scale scalePositive depth)
      (clusterRetainedEndpoint (rule.generation depth).network (configuration depth))
      (cluster_degree_positive (rule.generation depth).network (configuration depth) crossing)
      (diracProba initial)
      (fun point => if kind = 1 then 1 else
        (degree (clusterRetainedEndpoint (rule.generation depth).network (configuration depth)) point)⁻¹)
      (fun point => by
        split_ifs
        · exact zero_lt_one
        · exact inv_pos.mpr (cluster_degree_positive (rule.generation depth).network (configuration depth) crossing point))
      clock clockPositive id := by
  rw [actualFullConfigurationPathLaw_eq_placed]
  exact actualFiniteAnnealedPlacedPathLaw_weighted_configuration_transport
    rule configuration scale scalePositive depth crossing initial clock clockPositive kind notDiscrete id

end
end IGSIII34.Spectral
