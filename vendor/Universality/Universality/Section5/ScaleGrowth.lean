import Universality.Section5.GrowthDimensions
import Mathlib.Analysis.SpecificLimits.Basic

namespace Universality.Section5
open Filter

theorem explicit_scales_tendsto_atTop :
    Tendsto (fun index : ℕ => (19 * 661 ^ index) ^ 100) atTop atTop := by
  have powers : Tendsto (fun index : ℕ => 661 ^ index) atTop atTop :=
    tendsto_pow_atTop_atTop_of_one_lt (by norm_num)
  have products : Tendsto (fun index : ℕ => 19 * 661 ^ index) atTop atTop :=
    tendsto_atTop_mono (fun index => by omega) powers
  exact products.atTop_pow (by norm_num)

theorem compositionFamily_scales_tendsto_atTop {first repeated : Rule}
    (firstResponses : RuleResponses first 19)
    (repeatedResponses : RuleResponses repeated 661) :
    Tendsto (fun index : ℕ => (compositionFamily first repeated index).network.fullGraph.dist
      (compositionFamily first repeated index).network.source
      (compositionFamily first repeated index).network.target) atTop atTop := by
  simpa only [(compositionFamily_responses firstResponses repeatedResponses _).distance]
    using explicit_scales_tendsto_atTop

end Universality.Section5
