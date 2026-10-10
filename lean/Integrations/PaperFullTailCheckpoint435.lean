import Integrations.FiniteNaturalCheckpoint435

noncomputable section
namespace BinaryFormMoat.GeometryIntegration
open EntropyIntegration MeasureTheory ProbabilityTheory

abbrev PaperFullTailSource (A : Type*) (d M : ℕ) (g0 : ℝ) (k : ℕ) :=
  PairedWalkTailTerminalSource A (paperScheduleWindow d M g0) k
    ((paperScheduleList d M g0).length - k) (terminalSmoothingLength (paperScheduleMaxT d M))

variable {A : Type*} [Fintype A] [MeasurableSpace A] [MeasurableSingletonClass A]

/-- The one common terminal experiment, starting at any earlier retained law. -/
def paperFullTailLaw (z : ℕ → Point) (d M : ℕ) (g0 : ℝ) (b : A → ℕ) (k : ℕ)
    (ν : Measure (PairedWalkSource A (paperScheduleWindow d M g0) k)) :
    Measure (PaperFullTailSource A d M g0 k) :=
  pairedWalkTailTerminalLaw z (paperScheduleWindow d M g0) b k ν
    ((paperScheduleList d M g0).length - k) (terminalSmoothingLength (paperScheduleMaxT d M))

instance paperFullTailLaw_isProbabilityMeasure (z : ℕ → Point) (d M : ℕ) (g0 : ℝ)
    (b : A → ℕ) (k : ℕ) (ν : Measure (PairedWalkSource A (paperScheduleWindow d M g0) k))
    [IsProbabilityMeasure ν] : IsProbabilityMeasure (paperFullTailLaw z d M g0 b k ν) := by
  let : NeZero (terminalSmoothingLength (paperScheduleMaxT d M)) := ⟨(terminalSmoothingLength_pos _).ne'⟩
  unfold paperFullTailLaw
  infer_instance

omit [Fintype A] [MeasurableSpace A] [MeasurableSingletonClass A] in
def paperFullTailTerminalTime (d M : ℕ) (g0 : ℝ) (b : A → ℕ) (k : ℕ)
    (ω : PaperFullTailSource A d M g0 k) : ℕ :=
  pairedWalkTailTerminalTime (paperScheduleWindow d M g0) b k
    ((paperScheduleList d M g0).length - k) (terminalSmoothingLength (paperScheduleMaxT d M)) ω

omit [Fintype A] [MeasurableSpace A] [MeasurableSingletonClass A] in
/-- Read the actual unsmoothed checkpoint on this SAME common terminal source. -/
def paperFullTailCheckpointTime (d M : ℕ) (g0 : ℝ) (b : A → ℕ) (k q : ℕ)
    (hq : q ≤ (paperScheduleList d M g0).length) (ω : PaperFullTailSource A d M g0 k) : ℕ :=
  pairedWalkTime (paperScheduleWindow d M g0) b (k + (q - k))
    (pairedWalkTailCheckpoint (paperScheduleWindow d M g0) k ((paperScheduleList d M g0).length - k)
      (terminalSmoothingLength (paperScheduleMaxT d M)) (q - k) (Nat.sub_le_sub_right hq k) ω)

/-- Exact joint entropy of every checkpoint tuple; the terminal offset has
no effect on its law, even for an arbitrary earlier starting probability law. -/
theorem paperFullTailLaw_checkpoint_jointEntropy {ι Q : Type*} [Fintype ι] [Fintype Q]
    (z : ℕ → Point) (d M : ℕ) (g0 : ℝ) (b : A → ℕ) (k q : ℕ)
    (hq : q ≤ (paperScheduleList d M g0).length)
    (ν : Measure (PairedWalkSource A (paperScheduleWindow d M g0) k))
    (G : ι × Q → Type*) [∀ c, MeasurableSpace (G c)] (φ : ∀ c, Point → G c) (s : ℕ) :
    labelSubsetJointEntropy (paperFullTailLaw z d M g0 b k ν) G
      (fun c ω => φ c (z (paperFullTailCheckpointTime d M g0 b k q hq ω))) s =
      labelSubsetJointEntropy (pairedWalkTailLaw z (paperScheduleWindow d M g0) b k ν (q - k)) G
        (fun c ω => φ c (z (pairedWalkTime (paperScheduleWindow d M g0) b (k + (q - k)) ω))) s := by
  let : NeZero (terminalSmoothingLength (paperScheduleMaxT d M)) := ⟨(terminalSmoothingLength_pos _).ne'⟩
  exact pairedWalkTailTerminalLaw_checkpoint_jointEntropy z (paperScheduleWindow d M g0) b k ν
    ((paperScheduleList d M g0).length - k) (terminalSmoothingLength (paperScheduleMaxT d M))
    (q - k) (Nat.sub_le_sub_right hq k) G φ s

omit [Fintype A] [MeasurableSpace A] [MeasurableSingletonClass A] in
/-- The actual checkpoint time and common terminal time satisfy the physical
future bound of the ORIGINAL listed operation, under every measure and fiber. -/
theorem paperFullTailTerminalTime_checkpoint_bounds (d M : ℕ) (g0 : ℝ) (b : A → ℕ)
    (k q : ℕ) (hk : k ≤ q) (hq : q < (paperScheduleList d M g0).length)
    (ω : PaperFullTailSource A d M g0 k) :
    paperFullTailCheckpointTime d M g0 b k q hq.le ω ≤ paperFullTailTerminalTime d M g0 b k ω ∧
      paperFullTailTerminalTime d M g0 b k ω ≤ paperFullTailCheckpointTime d M g0 b k q hq.le ω +
        paperFutureShift ((paperScheduleList d M g0).get ⟨q, hq⟩) := by
  have he : k + (q - k) = q := by omega
  have h := paperTailTerminalTime_checkpoint_bounds b d M g0 k ((paperScheduleList d M g0).length - k)
    (terminalSmoothingLength (paperScheduleMaxT d M)) (q - k) le_rfl
    (Nat.sub_le_sub_right hq.le k) (by omega) (by omega) ω
  simpa only [paperFullTailCheckpointTime, paperFullTailTerminalTime, he] using h

/-- Original positive initial-time fibers remain fresh tail experiments.
The equality also covers zero fibers, without a probability instance there. -/
theorem paperFullTailLaw_cond_initial_time (z : ℕ → Point) (d M : ℕ) (g0 : ℝ)
    (b : A → ℕ) (k : ℕ) (hk : k ≤ (paperScheduleList d M g0).length)
    (ν : Measure (PairedWalkSource A (paperScheduleWindow d M g0) k)) [IsProbabilityMeasure ν]
    (a : ℕ) :
    (paperFullTailLaw z d M g0 b k ν)[|paperFullTailCheckpointTime d M g0 b k k hk ⁻¹' {a}] =
      paperFullTailLaw z d M g0 b k (ν[|pairedWalkTime (paperScheduleWindow d M g0) b k ⁻¹' {a}]) := by
  let : NeZero (terminalSmoothingLength (paperScheduleMaxT d M)) := ⟨(terminalSmoothingLength_pos _).ne'⟩
  have transport (j : ℕ) (hj : j ≤ (paperScheduleList d M g0).length - k)
      (hj0 : j = 0) (ω : PaperFullTailSource A d M g0 k) :
      pairedWalkTime (paperScheduleWindow d M g0) b (k + j)
        (pairedWalkTailCheckpoint (paperScheduleWindow d M g0) k
          ((paperScheduleList d M g0).length - k)
          (terminalSmoothingLength (paperScheduleMaxT d M)) j hj ω) =
        pairedWalkTime (paperScheduleWindow d M g0) b k
          (pairedWalkPast (paperScheduleWindow d M g0) k
            ((paperScheduleList d M g0).length - k) ω.1) := by
    subst j
    dsimp only [pairedWalkTailCheckpoint, Nat.add_zero]
    rw [pairedWalkCheckpoint_add]
  have hreader : paperFullTailCheckpointTime d M g0 b k k hk =
      (fun ω => pairedWalkTime (paperScheduleWindow d M g0) b k
        (pairedWalkPast (paperScheduleWindow d M g0) k
          ((paperScheduleList d M g0).length - k) ω.1)) := by
    funext ω
    exact transport (k - k) (Nat.sub_le_sub_right hk k) (Nat.sub_self k) ω
  rw [hreader]
  unfold paperFullTailLaw
  exact pairedWalkTailTerminalLaw_cond_checkpoint z (paperScheduleWindow d M g0) b k ν
    ((paperScheduleList d M g0).length - k) (terminalSmoothingLength (paperScheduleMaxT d M))
    (pairedWalkTime (paperScheduleWindow d M g0) b k) a

end BinaryFormMoat.GeometryIntegration
#print axioms BinaryFormMoat.GeometryIntegration.PaperFullTailSource
#print axioms BinaryFormMoat.GeometryIntegration.paperFullTailLaw
#print axioms BinaryFormMoat.GeometryIntegration.paperFullTailLaw_isProbabilityMeasure
#print axioms BinaryFormMoat.GeometryIntegration.paperFullTailTerminalTime
#print axioms BinaryFormMoat.GeometryIntegration.paperFullTailCheckpointTime
#print axioms BinaryFormMoat.GeometryIntegration.paperFullTailLaw_checkpoint_jointEntropy
#print axioms BinaryFormMoat.GeometryIntegration.paperFullTailTerminalTime_checkpoint_bounds
#print axioms BinaryFormMoat.GeometryIntegration.paperFullTailLaw_cond_initial_time
