import IGSIII34.Forms.AnchoredCompleteness

/-! The complete Hilbert structure of anchored finite skeleton energy. -/
set_option autoImplicit false
set_option linter.unusedSectionVars false
namespace IGSIII34.Forms
noncomputable section
open IGSIII34.ResistanceLimit Filter
open scoped Topology

variable {Carrier : Type*} [MetricSpace Carrier]
variable {Edge : ℕ → Type*} [∀ depth, Fintype (Edge depth)]
variable (endpoint : ∀ depth, Edge depth → Carrier × Carrier)
variable (conductance : ∀ depth, Edge depth → ℝ)
variable (nonnegative : ∀ depth edge, 0 ≤ conductance depth edge)
variable (monotone : ∀ potential, Monotone (fun depth => traceEnergy endpoint conductance depth potential))
variable (resistanceBound : ∀ potential ∈ energyDomain endpoint conductance nonnegative,
  ∀ first second, (potential first - potential second) ^ 2 ≤
    dist first second * limitingEnergy endpoint conductance potential)

@[reducible] def anchoredNormedAddCommGroup (anchor : Carrier) :
    NormedAddCommGroup (energyDomain endpoint conductance nonnegative) := by
  letI := anchoredInnerCore endpoint conductance nonnegative monotone resistanceBound anchor
  exact InnerProductSpace.Core.toNormedAddCommGroup (𝕜 := ℝ)

theorem anchored_norm_square (anchor : Carrier) :
    letI := anchoredNormedAddCommGroup endpoint conductance nonnegative monotone resistanceBound anchor
    ∀ potential : energyDomain endpoint conductance nonnegative,
      ‖potential‖ ^ 2 = anchoredSquare endpoint conductance anchor potential.val := by
  intro potential
  change (Real.sqrt (limitingPairing endpoint conductance potential.val potential.val +
      potential.val anchor * potential.val anchor)) ^ 2 = _
  rw [limitingPairing_self endpoint conductance nonnegative monotone potential.property]
  rw [Real.sq_sqrt (add_nonneg
    (limitingEnergy_nonnegative endpoint conductance nonnegative potential.property) (mul_self_nonneg _))]
  dsimp only [anchoredSquare]
  ring

@[reducible] def anchoredInnerProductSpace (anchor : Carrier) :
    letI := anchoredNormedAddCommGroup endpoint conductance nonnegative monotone resistanceBound anchor
    InnerProductSpace ℝ (energyDomain endpoint conductance nonnegative) := by
  letI := anchoredInnerCore endpoint conductance nonnegative monotone resistanceBound anchor
  letI := anchoredNormedAddCommGroup endpoint conductance nonnegative monotone resistanceBound anchor
  exact InnerProductSpace.ofCore (inferInstance :
    PreInnerProductSpace.Core ℝ (energyDomain endpoint conductance nonnegative))

theorem anchored_completeSpace (anchor : Carrier) :
    letI := anchoredNormedAddCommGroup endpoint conductance nonnegative monotone resistanceBound anchor
    letI : UniformSpace (energyDomain endpoint conductance nonnegative) :=
      (anchoredNormedAddCommGroup endpoint conductance nonnegative monotone resistanceBound anchor).toMetricSpace.toUniformSpace
    CompleteSpace (energyDomain endpoint conductance nonnegative) := by
  letI := anchoredNormedAddCommGroup endpoint conductance nonnegative monotone resistanceBound anchor
  letI : UniformSpace (energyDomain endpoint conductance nonnegative) :=
    (anchoredNormedAddCommGroup endpoint conductance nonnegative monotone resistanceBound anchor).toMetricSpace.toUniformSpace
  apply Metric.complete_of_cauchySeq_tendsto
  intro sequence cauchy
  have energyCauchy : ∀ epsilon > 0, ∃ threshold : ℕ,
      ∀ first ≥ threshold, ∀ second ≥ threshold,
        anchoredSquare endpoint conductance anchor
          (fun point => (sequence first).val point - (sequence second).val point) ≤ epsilon := by
    intro epsilon positive
    obtain ⟨threshold, bounded⟩ := Metric.cauchySeq_iff.mp cauchy
      (Real.sqrt epsilon) (Real.sqrt_pos.mpr positive)
    refine ⟨threshold, ?_⟩
    intro first firstAfter second secondAfter
    have small := bounded first firstAfter second secondAfter
    rw [dist_eq_norm] at small
    have square := anchored_norm_square endpoint conductance nonnegative monotone resistanceBound anchor
      (sequence first - sequence second)
    change ‖sequence first - sequence second‖ ^ 2 =
      anchoredSquare endpoint conductance anchor
        (fun point => (sequence first).val point - (sequence second).val point) at square
    nlinarith [Real.sq_sqrt positive.le, norm_nonneg (sequence first - sequence second)]
  obtain ⟨limit, pointwise, energyConvergence⟩ := exists_energy_limit_of_cauchy endpoint conductance
    nonnegative anchor sequence resistanceBound energyCauchy
  refine ⟨limit, Metric.tendsto_atTop.mpr ?_⟩
  intro epsilon positive
  obtain ⟨threshold, bounded⟩ := (eventually_atTop.mp
    (energyConvergence (epsilon ^ 2 / 2) (by positivity)))
  refine ⟨threshold, ?_⟩
  intro index after
  have small := bounded index after
  have square := anchored_norm_square endpoint conductance nonnegative monotone resistanceBound anchor
    (sequence index - limit)
  change ‖sequence index - limit‖ ^ 2 =
    anchoredSquare endpoint conductance anchor
      (fun point => (sequence index).val point - limit.val point) at square
  rw [dist_eq_norm]
  nlinarith [norm_nonneg (sequence index - limit)]

end
end IGSIII34.Forms
