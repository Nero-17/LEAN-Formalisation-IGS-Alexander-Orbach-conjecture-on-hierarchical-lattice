import IGSIII34.Diffusion.UsualLocalJ1WeakTests

set_option autoImplicit false
set_option maxHeartbeats 2200000
namespace IGSIII34.Diffusion
noncomputable section
open MeasureTheory Filter Set
open scoped Topology NNReal

variable {Space : Type*} [MetricSpace Space] [CompactSpace Space]

/-- The usual-local J1 sequence criterion on genuine cadlag paths. The
limiting endpoint must be a continuity point; integer endpoints are not
given any special status. -/
def usualLocalJ1SequenceConvergence
    (paths : ℕ → SkorokhodCadlagPathCompletion Space)
    (path : SkorokhodCadlagPathCompletion Space) : Prop :=
  ∀ horizon : ℝ≥0, ContinuousAt path.val.toFun horizon →
    Tendsto (fun index => skorokhodHorizonRestrictionCompletion horizon (paths index).val)
      atTop (𝓝 (skorokhodHorizonRestrictionCompletion horizon path.val))

/-- The sequential topology determined by the standard usual-local J1
criterion. It is a genuine topology on the cadlag carrier, independent of
the integer-horizon topology. Metrization and comparison of the two Borel
spaces are separate statements, not silently asserted by this definition. -/
@[reducible]
def usualLocalJ1SequenceTopology : TopologicalSpace (SkorokhodCadlagPathCompletion Space) where
  IsOpen set := ∀ paths path, usualLocalJ1SequenceConvergence paths path →
    path ∈ set → ∀ᶠ index in atTop, paths index ∈ set
  isOpen_univ := by
    intro paths path convergence member
    exact Eventually.of_forall (fun _ => Set.mem_univ _)
  isOpen_inter := by
    intro first last firstOpen lastOpen paths path convergence member
    exact (firstOpen paths path convergence member.1).and
      (lastOpen paths path convergence member.2)
  isOpen_sUnion := by
    intro collection openSets paths path convergence member
    obtain ⟨set, belongs, inside⟩ := Set.mem_sUnion.mp member
    filter_upwards [openSets set belongs paths path convergence inside] with index membership
    exact Set.mem_sUnion.mpr ⟨set, belongs, membership⟩

/-- Every sequence satisfying the standard local-J1 criterion converges
in the topology constructed from that criterion. -/
theorem usualLocalJ1Sequence_tendsto
    (paths : ℕ → SkorokhodCadlagPathCompletion Space)
    (path : SkorokhodCadlagPathCompletion Space)
    (convergence : usualLocalJ1SequenceConvergence paths path) :
    Tendsto paths atTop (@nhds _ usualLocalJ1SequenceTopology path) := by
  letI : TopologicalSpace (SkorokhodCadlagPathCompletion Space) := usualLocalJ1SequenceTopology
  apply tendsto_nhds.mpr
  intro set openSet membership
  exact openSet paths path convergence membership

/-- The test criterion used in the weak-integral wrapper is exactly
topological continuity for the local-J1 sequential topology. -/
theorem usualLocalJ1Test_continuous_iff
    (test : SkorokhodCadlagPathCompletion Space → ℝ) :
    Continuous[usualLocalJ1SequenceTopology, inferInstance] test ↔
      usualLocalJ1SequentiallyContinuousTest test := by
  letI : TopologicalSpace (SkorokhodCadlagPathCompletion Space) := usualLocalJ1SequenceTopology
  constructor
  · intro continuity path paths convergence
    exact (continuity.tendsto path).comp (usualLocalJ1Sequence_tendsto paths path convergence)
  · intro continuity
    apply continuous_def.mpr
    intro set openSet
    change ∀ paths path, usualLocalJ1SequenceConvergence paths path →
      test path ∈ set → ∀ᶠ index in atTop, test (paths index) ∈ set
    intro paths path convergence membership
    exact (continuity path paths convergence).eventually (openSet.mem_nhds membership)

/-- Local-J1 continuous tests are Borel measurable for the explicitly
constructed local-J1 topology. The weak wrapper separately specifies the
Borel measurability used by its original integer-horizon probability laws. -/
theorem usualLocalJ1Test_local_borel_measurable
    (test : SkorokhodCadlagPathCompletion Space → ℝ)
    (continuity : usualLocalJ1SequentiallyContinuousTest test) :
    @Measurable (SkorokhodCadlagPathCompletion Space) ℝ
      (@borel _ usualLocalJ1SequenceTopology) (borel ℝ) test := by
  letI : TopologicalSpace (SkorokhodCadlagPathCompletion Space) := usualLocalJ1SequenceTopology
  letI : MeasurableSpace (SkorokhodCadlagPathCompletion Space) := borel _
  letI : BorelSpace (SkorokhodCadlagPathCompletion Space) := ⟨rfl⟩
  exact (usualLocalJ1Test_continuous_iff test).mpr continuity |>.measurable

/-- Any sequential topology with the standard local-J1 sequence criterion
is exactly the topology constructed here. In particular this comparison
applies to any metrization after its usual sequence criterion is proved.
It does not assume a stochastic-process existence or convergence theorem. -/
theorem usualLocalJ1SequenceTopology_eq_of_sequence_criterion
    (topology : TopologicalSpace (SkorokhodCadlagPathCompletion Space))
    (sequential : @SequentialSpace (SkorokhodCadlagPathCompletion Space) topology)
    (criterion : ∀ (paths : ℕ → SkorokhodCadlagPathCompletion Space)
      (path : SkorokhodCadlagPathCompletion Space),
      Tendsto paths atTop (@nhds _ topology path) ↔ usualLocalJ1SequenceConvergence paths path) :
    topology = usualLocalJ1SequenceTopology := by
  letI : TopologicalSpace (SkorokhodCadlagPathCompletion Space) := topology
  letI : SequentialSpace (SkorokhodCadlagPathCompletion Space) := sequential
  apply TopologicalSpace.ext
  funext set
  apply propext
  change IsOpen set ↔ ∀ paths path, usualLocalJ1SequenceConvergence paths path →
    path ∈ set → ∀ᶠ index in atTop, paths index ∈ set
  constructor
  · intro openSet paths path convergence membership
    exact ((criterion paths path).mpr convergence).eventually (openSet.mem_nhds membership)
  · intro sequentiallyOpen
    have complementClosed : IsSeqClosed setᶜ := by
      intro paths path outside convergence
      intro membership
      obtain ⟨index, inside⟩ :=
        (sequentiallyOpen paths path ((criterion paths path).mp convergence) membership).exists
      exact outside index inside
    simpa only [compl_compl] using complementClosed.isClosed.isOpen_compl

end
end IGSIII34.Diffusion
