import IGSIII34.Spectral.CompactEmbedding
import Mathlib.MeasureTheory.Function.LpSpace.ContinuousFunctions

set_option autoImplicit false

namespace IGSIII34.Diffusion
noncomputable section
open MeasureTheory Filter Topology Set
open scoped BoundedContinuousFunction

/-- On a compact family of continuous potentials, full support upgrades
strong L² convergence to uniform convergence. Compactness is checked in
the sup norm; it can therefore be obtained from the proved resistance
form-ball embedding rather than postulated process regularity. -/
theorem compact_family_L2_to_uniform_completion20261011
    {Carrier Index : Type*} [TopologicalSpace Carrier] [MeasurableSpace Carrier] [BorelSpace Carrier]
    (measure : Measure Carrier) [IsFiniteMeasure measure] [measure.IsOpenPosMeasure]
    (family : Set (Carrier →ᵇ ℝ)) (compact : IsCompact family)
    (potentials : Index → family) (limit : family) (filter : Filter Index)
    (L2Converges : Tendsto (fun index => BoundedContinuousFunction.toLp 2 measure ℝ (potentials index).val)
      filter (𝓝 (BoundedContinuousFunction.toLp 2 measure ℝ limit.val))) :
    Tendsto (fun index => (potentials index).val) filter (𝓝 limit.val) := by
  letI : CompactSpace family := isCompact_iff_compactSpace.mp compact
  have embedding : IsClosedEmbedding
      (fun potential : family => BoundedContinuousFunction.toLp 2 measure ℝ potential.val) :=
    ((BoundedContinuousFunction.toLp 2 measure ℝ).continuous.comp continuous_subtype_val).isClosedEmbedding
      ((BoundedContinuousFunction.toLp_injective measure).comp Subtype.val_injective)
  have subtypeConverges : Tendsto potentials filter (𝓝 limit) :=
    embedding.tendsto_nhds_iff.mpr L2Converges
  exact continuous_subtype_val.tendsto limit |>.comp subtypeConverges

end
end IGSIII34.Diffusion
