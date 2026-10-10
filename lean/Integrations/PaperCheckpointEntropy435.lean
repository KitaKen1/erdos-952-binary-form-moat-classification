import Integrations.PaperTerminalHistory435

noncomputable section
namespace BinaryFormMoat.GeometryIntegration
open EntropyIntegration MeasureTheory ProbabilityTheory

section CommonHistory
variable {A : Type*} [Fintype A] [MeasurableSpace A] [MeasurableSingletonClass A]
  (z : ℕ → Point) (b : A → ℕ) (d M : ℕ) (g0 : ℝ) (R : ℕ)
  (hstep : ∀ t, sqDist (z (t + 1)) (z t) ≤ (R : ℤ))
  (k : Fin (paperScheduleList d M g0).length)

include hstep

omit [Fintype A] [MeasurableSpace A] [MeasurableSingletonClass A] in
/-- The actual common-source displacement is bounded for EVERY history,
so the same alphabet also works under any earlier-event conditional law. -/
theorem paperCheckpoint_displacement_mem (ω : PaperTerminalSource A d M g0) :
    z (paperTerminalTime b d M g0 ω) - z (paperCheckpointTime b d M g0 k.castSucc ω) ∈
      displacementBox ((R + 1) * paperFutureShift ((paperScheduleList d M g0).get k)) := by
  have ht := paperTerminalTime_checkpoint_bounds b d M g0 k ω
  exact walk_displacement_mem z (R + 1) (sqDist_walk_coordinate_steps z R hstep)
    _ _ _ ht.1 ht.2

/-- No change of source law or independence premise: the deterministic
history bound supplies the displacement entropy on this same source. -/
theorem paperCheckpoint_displacement_entropy_le (ν : Measure (PaperTerminalSource A d M g0)) :
    entropy (fun ω => z (paperTerminalTime b d M g0 ω) -
      z (paperCheckpointTime b d M g0 k.castSucc ω)) ν ≤
        2 * Real.log (2 * ((R + 1) * paperFutureShift ((paperScheduleList d M g0).get k)) + 1 : ℕ) := by
  have h := entropy_le_log_card_of_mem
    (A := displacementBox ((R + 1) * paperFutureShift ((paperScheduleList d M g0).get k)))
    (measurable_of_finite (fun ω => z (paperTerminalTime b d M g0 ω) -
      z (paperCheckpointTime b d M g0 k.castSucc ω)))
    (ae_of_all ν (paperCheckpoint_displacement_mem z b d M g0 R hstep k))
  simpa only [displacementBox_card, Nat.cast_pow, Real.log_pow, Nat.cast_ofNat] using h

theorem paperCheckpoint_displacement_entropy_budget
    (ν : Measure (PaperTerminalSource A d M g0))
    (hlog : Real.log (paperFutureShift ((paperScheduleList d M g0).get k) + 1 : ℕ) ≤
      2 * (paperOpG ((paperScheduleList d M g0).get k) * paperOpU ((paperScheduleList d M g0).get k))) :
    entropy (fun ω => z (paperTerminalTime b d M g0 ω) -
      z (paperCheckpointTime b d M g0 k.castSucc ω)) ν ≤
        4 * (paperOpG ((paperScheduleList d M g0).get k) * paperOpU ((paperScheduleList d M g0).get k)) +
          2 * Real.log (2 * (R + 1) + 1 : ℕ) :=
  (paperCheckpoint_displacement_entropy_le z b d M g0 R hstep k ν).trans
    (paperFutureShift_displacement_log_bound _ R hlog)

/-- Exact original checkpoint tuple entropy persists at the terminal time;
the physical displacement cost is charged ONCE to the whole joint tuple. -/
theorem paperCheckpoint_jointEntropy_transport {ι Q : Type*}
    [Fintype ι] [Fintype Q] [Nonempty Q] (μ : Measure A) [IsProbabilityMeasure μ]
    (G : ι × Q → Type*) [∀ c, Fintype (G c)] [∀ c, MeasurableSpace (G c)]
    [∀ c, MeasurableSingletonClass (G c)] [∀ c, AddCommGroup (G c)]
    (φ : ∀ c, Point →+ G c) (s : ℕ) (hs : s ≤ Fintype.card ι) :
    labelSubsetJointEntropy (pairedWalkLaw z (paperScheduleWindow d M g0) μ b k.val) G
      (fun c ω => φ c (z (pairedWalkTime (paperScheduleWindow d M g0) b k.val ω))) s -
        2 * Real.log (2 * ((R + 1) * paperFutureShift ((paperScheduleList d M g0).get k)) + 1 : ℕ) ≤
      labelSubsetJointEntropy (paperTerminalLaw z μ b d M g0) G
        (fun c ω => φ c (z (paperTerminalTime b d M g0 ω))) s := by
  have hl := labelSubsetJointEntropy_loss_le_displacement (paperTerminalLaw z μ b d M g0) G
    (fun c ω => φ c (z (paperCheckpointTime b d M g0 k.castSucc ω)))
    (fun c ω => φ c (z (paperTerminalTime b d M g0 ω)))
    (fun ω => z (paperTerminalTime b d M g0 ω) - z (paperCheckpointTime b d M g0 k.castSucc ω))
    (fun c => φ c) (by intro c ω; rw [map_sub]; abel) s hs
  rw [paperTerminalLaw_checkpoint_jointEntropy] at hl
  have hu := paperCheckpoint_displacement_entropy_le z b d M g0 R hstep k
    (paperTerminalLaw z μ b d M g0)
  simp only [Fin.val_castSucc] at hl
  linarith


/-- The source-scale version pays 4gU plus the fixed step-alphabet constant. -/
theorem paperCheckpoint_jointEntropy_budget {ι Q : Type*}
    [Fintype ι] [Fintype Q] [Nonempty Q] (μ : Measure A) [IsProbabilityMeasure μ]
    (G : ι × Q → Type*) [∀ c, Fintype (G c)] [∀ c, MeasurableSpace (G c)]
    [∀ c, MeasurableSingletonClass (G c)] [∀ c, AddCommGroup (G c)]
    (φ : ∀ c, Point →+ G c) (s : ℕ) (hs : s ≤ Fintype.card ι)
    (hlog : Real.log (paperFutureShift ((paperScheduleList d M g0).get k) + 1 : ℕ) ≤
      2 * (paperOpG ((paperScheduleList d M g0).get k) * paperOpU ((paperScheduleList d M g0).get k))) :
    labelSubsetJointEntropy (pairedWalkLaw z (paperScheduleWindow d M g0) μ b k.val) G
      (fun c ω => φ c (z (pairedWalkTime (paperScheduleWindow d M g0) b k.val ω))) s -
        (4 * (paperOpG ((paperScheduleList d M g0).get k) * paperOpU ((paperScheduleList d M g0).get k)) +
          2 * Real.log (2 * (R + 1) + 1 : ℕ)) ≤
      labelSubsetJointEntropy (paperTerminalLaw z μ b d M g0) G
        (fun c ω => φ c (z (paperTerminalTime b d M g0 ω))) s := by
  have ht := paperCheckpoint_jointEntropy_transport z b d M g0 R hstep k μ G φ s hs
  have hc := paperFutureShift_displacement_log_bound ((paperScheduleList d M g0).get k) R hlog
  linarith

end CommonHistory

/-- Choose the threshold BEFORE the finite source, walk, starting times,
step bound, checkpoint and source measure. It works for every operation,
including any conditional law on the same finite terminal source. -/
theorem paperSchedule_uniform_checkpoint_entropy (d : ℕ) (hd : 1 ≤ d) (g0 : ℝ)
    (hg0 : 0 < g0) (hg01 : g0 < 1) :
    ∃ M0 : ℕ, ∀ M ≥ M0, ∀ (A : Type*) [Fintype A] [MeasurableSpace A]
      [MeasurableSingletonClass A] (z : ℕ → Point) (b : A → ℕ) (R : ℕ)
      (_ : ∀ t, sqDist (z (t + 1)) (z t) ≤ (R : ℤ))
      (k : Fin (paperScheduleList d M g0).length) (ν : Measure (PaperTerminalSource A d M g0)),
      entropy (fun ω => z (paperTerminalTime b d M g0 ω) -
        z (paperCheckpointTime b d M g0 k.castSucc ω)) ν ≤
          4 * (paperOpG ((paperScheduleList d M g0).get k) * paperOpU ((paperScheduleList d M g0).get k)) +
            2 * Real.log (2 * (R + 1) + 1 : ℕ) := by
  obtain ⟨M0, hM0⟩ := paperSchedule_uniform_future_shift d hd g0 hg0 hg01
  refine ⟨M0, ?_⟩
  intro M hM A _ _ _ z b R hstep k ν
  exact paperCheckpoint_displacement_entropy_budget z b d M g0 R hstep k ν
    (hM0 M hM _ (paperScheduleList_get_mem d M g0 k))

/-- Event smoothing is now applied to the actual common terminal time law,
without assuming its equality to an abstract smoothed law. -/
theorem paperTerminalLaw_shift_event_bound {A : Type*} [Fintype A]
    [MeasurableSpace A] [MeasurableSingletonClass A]
    (z : ℕ → Point) (μ : Measure A) [IsProbabilityMeasure μ] (b : A → ℕ)
    (d M : ℕ) (g0 : ℝ) (E : Set ℕ) (a : ℕ) (ha : (a : ℝ) ≤ paperScheduleMaxT d M) :
    |((paperTerminalLaw z μ b d M g0).map (paperTerminalTime b d M g0)).real
        ((fun t => t + a) ⁻¹' E) -
      ((paperTerminalLaw z μ b d M g0).map (paperTerminalTime b d M g0)).real E| ≤
        1 / paperScheduleMaxT d M ^ 9 := by
  rw [paperTerminalLaw_time_map]
  exact paper_terminal_smoothing_event_bound (paperHistoryLaw z μ b d M g0) _ E a d M ha

end BinaryFormMoat.GeometryIntegration

#print axioms BinaryFormMoat.GeometryIntegration.paperCheckpoint_displacement_mem
#print axioms BinaryFormMoat.GeometryIntegration.paperCheckpoint_displacement_entropy_le
#print axioms BinaryFormMoat.GeometryIntegration.paperCheckpoint_displacement_entropy_budget
#print axioms BinaryFormMoat.GeometryIntegration.paperCheckpoint_jointEntropy_transport
#print axioms BinaryFormMoat.GeometryIntegration.paperCheckpoint_jointEntropy_budget
#print axioms BinaryFormMoat.GeometryIntegration.paperSchedule_uniform_checkpoint_entropy
#print axioms BinaryFormMoat.GeometryIntegration.paperTerminalLaw_shift_event_bound
