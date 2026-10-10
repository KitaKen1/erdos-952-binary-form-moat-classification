import Integrations.PaperScheduleWindows435
import Integrations.PairedWalkHistory435

noncomputable section
namespace BinaryFormMoat.GeometryIntegration
open EntropyIntegration MeasureTheory ProbabilityTheory

abbrev PaperHistorySource (A : Type*) (d M : ℕ) (g0 : ℝ) :=
  PairedWalkSource A (paperScheduleWindow d M g0) (paperScheduleList d M g0).length

abbrev PaperTerminalSource (A : Type*) (d M : ℕ) (g0 : ℝ) :=
  PaperHistorySource A d M g0 × Fin (terminalSmoothingLength (paperScheduleMaxT d M))

variable {A : Type*} [Fintype A] [MeasurableSpace A] [MeasurableSingletonClass A]

def paperHistoryLaw (z : ℕ → Point) (μ : Measure A) (b : A → ℕ) (d M : ℕ) (g0 : ℝ) :
    Measure (PaperHistorySource A d M g0) :=
  pairedWalkLaw z (paperScheduleWindow d M g0) μ b (paperScheduleList d M g0).length

instance paperHistoryLaw_isProbabilityMeasure (z : ℕ → Point) (μ : Measure A)
    [IsProbabilityMeasure μ] (b : A → ℕ) (d M : ℕ) (g0 : ℝ) :
    IsProbabilityMeasure (paperHistoryLaw z μ b d M g0) := by
  unfold paperHistoryLaw
  infer_instance

/-- ONE common terminal source/law runs the entire actual schedule, then adds
an independent uniform offset. It contains every earlier exact history. -/
def paperTerminalLaw (z : ℕ → Point) (μ : Measure A) (b : A → ℕ) (d M : ℕ) (g0 : ℝ) :
    Measure (PaperTerminalSource A d M g0) :=
  (paperHistoryLaw z μ b d M g0).prod
    (uniformOn (Set.univ : Set (Fin (terminalSmoothingLength (paperScheduleMaxT d M)))))

instance paperTerminalLaw_isProbabilityMeasure (z : ℕ → Point) (μ : Measure A)
    [IsProbabilityMeasure μ] (b : A → ℕ) (d M : ℕ) (g0 : ℝ) :
    IsProbabilityMeasure (paperTerminalLaw z μ b d M g0) := by
  let : NeZero (terminalSmoothingLength (paperScheduleMaxT d M)) :=
    ⟨(terminalSmoothingLength_pos _).ne'⟩
  unfold paperTerminalLaw
  infer_instance

def paperTerminalTime (b : A → ℕ) (d M : ℕ) (g0 : ℝ) (ω : PaperTerminalSource A d M g0) : ℕ :=
  pairedWalkTime (paperScheduleWindow d M g0) b (paperScheduleList d M g0).length ω.1 + ω.2.val

def paperCheckpointHistory (d M : ℕ) (g0 : ℝ)
    (k : Fin ((paperScheduleList d M g0).length + 1)) (ω : PaperTerminalSource A d M g0) :
    PairedWalkSource A (paperScheduleWindow d M g0) k.val :=
  pairedWalkCheckpoint (paperScheduleWindow d M g0) (paperScheduleList d M g0).length k ω.1

def paperCheckpointTime (b : A → ℕ) (d M : ℕ) (g0 : ℝ)
    (k : Fin ((paperScheduleList d M g0).length + 1)) (ω : PaperTerminalSource A d M g0) : ℕ :=
  pairedWalkTime (paperScheduleWindow d M g0) b k.val (paperCheckpointHistory d M g0 k ω)

omit [Fintype A] [MeasurableSpace A] [MeasurableSingletonClass A] in
/-- S is now an ACTUAL history-time bound, not merely a numeric schedule sum. -/
theorem paperTerminalTime_checkpoint_bounds (b : A → ℕ) (d M : ℕ) (g0 : ℝ)
    (k : Fin (paperScheduleList d M g0).length) (ω : PaperTerminalSource A d M g0) :
    paperCheckpointTime b d M g0 k.castSucc ω ≤ paperTerminalTime b d M g0 ω ∧
      paperTerminalTime b d M g0 ω ≤ paperCheckpointTime b d M g0 k.castSucc ω +
        paperFutureShift ((paperScheduleList d M g0).get k) := by
  have ht := pairedWalkCheckpoint_time_bounds (paperScheduleWindow d M g0) b
    (paperScheduleList d M g0).length k.castSucc ω.1
  have hs := paperScheduleWindow_suffix_sum_le d M g0 k
    ((paperScheduleList d M g0).length - k.val) le_rfl
  have ho : ω.2.val ≤ terminalSmoothingLength (paperScheduleMaxT d M) - 1 := by
    have h := ω.2.isLt
    omega
  dsimp [paperCheckpointTime, paperCheckpointHistory, paperTerminalTime]
  unfold paperFutureShift
  simp only [Fin.val_castSucc] at ht
  simp only [List.get_eq_getElem] at hs
  constructor <;> omega

/-- The common terminal source retains the exact earlier history law. -/
theorem paperTerminalLaw_checkpoint_map (z : ℕ → Point) (μ : Measure A) (b : A → ℕ)
    (d M : ℕ) (g0 : ℝ) (k : Fin ((paperScheduleList d M g0).length + 1)) :
    (paperTerminalLaw z μ b d M g0).map (paperCheckpointHistory d M g0 k) =
      pairedWalkLaw z (paperScheduleWindow d M g0) μ b k.val := by
  let : NeZero (terminalSmoothingLength (paperScheduleMaxT d M)) :=
    ⟨(terminalSmoothingLength_pos _).ne'⟩
  change ((paperHistoryLaw z μ b d M g0).prod _).map
    (pairedWalkCheckpoint (paperScheduleWindow d M g0) (paperScheduleList d M g0).length k ∘ Prod.fst) = _
  rw [← Measure.map_map (measurable_of_finite _) measurable_fst, Measure.map_fst_prod,
    measure_univ, one_smul]
  exact pairedWalkCheckpoint_law_map z _ μ b _ k

omit [MeasurableSingletonClass A] in
theorem paperTerminalLaw_time_map (z : ℕ → Point) (μ : Measure A) (b : A → ℕ)
    (d M : ℕ) (g0 : ℝ) :
    (paperTerminalLaw z μ b d M g0).map (paperTerminalTime b d M g0) =
      smoothedTimeLaw (paperHistoryLaw z μ b d M g0)
        (pairedWalkTime (paperScheduleWindow d M g0) b (paperScheduleList d M g0).length)
        (terminalSmoothingLength (paperScheduleMaxT d M)) := rfl

theorem paperTerminalLaw_checkpoint_identDistrib {S : Type*} [MeasurableSpace S]
    (z : ℕ → Point) (μ : Measure A) (b : A → ℕ) (d M : ℕ) (g0 : ℝ)
    (k : Fin ((paperScheduleList d M g0).length + 1))
    (F : PairedWalkSource A (paperScheduleWindow d M g0) k.val → S) :
    IdentDistrib (fun ω => F (paperCheckpointHistory d M g0 k ω)) F
      (paperTerminalLaw z μ b d M g0) (pairedWalkLaw z (paperScheduleWindow d M g0) μ b k.val) := by
  refine ⟨(measurable_of_finite _).aemeasurable, (measurable_of_finite _).aemeasurable, ?_⟩
  change (paperTerminalLaw z μ b d M g0).map (F ∘ paperCheckpointHistory d M g0 k) = _
  rw [← Measure.map_map (measurable_of_finite _) (measurable_of_finite _),
    paperTerminalLaw_checkpoint_map]

theorem paperTerminalLaw_checkpoint_jointEntropy {ι Q : Type*} [Fintype ι] [Fintype Q]
    (z : ℕ → Point) (μ : Measure A) (b : A → ℕ) (d M : ℕ) (g0 : ℝ)
    (k : Fin ((paperScheduleList d M g0).length + 1)) (G : ι × Q → Type*)
    [∀ c, MeasurableSpace (G c)] (φ : ∀ c, Point → G c) (s : ℕ) :
    labelSubsetJointEntropy (paperTerminalLaw z μ b d M g0) G
      (fun c ω => φ c (z (paperCheckpointTime b d M g0 k ω))) s =
      labelSubsetJointEntropy (pairedWalkLaw z (paperScheduleWindow d M g0) μ b k.val) G
        (fun c ω => φ c (z (pairedWalkTime (paperScheduleWindow d M g0) b k.val ω))) s := by
  unfold labelSubsetJointEntropy
  congr 1
  funext S ρ
  exact (paperTerminalLaw_checkpoint_identDistrib z μ b d M g0 k
    (fun ω (i : S) => φ (i.1, ρ i.1)
      (z (pairedWalkTime (paperScheduleWindow d M g0) b k.val ω)))).entropy_congr

end BinaryFormMoat.GeometryIntegration

#print axioms BinaryFormMoat.GeometryIntegration.PaperHistorySource
#print axioms BinaryFormMoat.GeometryIntegration.PaperTerminalSource
#print axioms BinaryFormMoat.GeometryIntegration.paperHistoryLaw
#print axioms BinaryFormMoat.GeometryIntegration.paperHistoryLaw_isProbabilityMeasure
#print axioms BinaryFormMoat.GeometryIntegration.paperTerminalLaw
#print axioms BinaryFormMoat.GeometryIntegration.paperTerminalLaw_isProbabilityMeasure
#print axioms BinaryFormMoat.GeometryIntegration.paperTerminalTime
#print axioms BinaryFormMoat.GeometryIntegration.paperCheckpointHistory
#print axioms BinaryFormMoat.GeometryIntegration.paperCheckpointTime
#print axioms BinaryFormMoat.GeometryIntegration.paperTerminalTime_checkpoint_bounds
#print axioms BinaryFormMoat.GeometryIntegration.paperTerminalLaw_checkpoint_map
#print axioms BinaryFormMoat.GeometryIntegration.paperTerminalLaw_time_map
#print axioms BinaryFormMoat.GeometryIntegration.paperTerminalLaw_checkpoint_identDistrib
#print axioms BinaryFormMoat.GeometryIntegration.paperTerminalLaw_checkpoint_jointEntropy
