import Integrations.PaperFullTailCheckpoint435
import Integrations.WalkWordBudget435

noncomputable section
namespace BinaryFormMoat.GeometryIntegration
open EntropyIntegration MeasureTheory ProbabilityTheory

/-- Exact terminal natural-time law of the SAME original full-tail
experiment. No replacement of the walk law or conditioning is made. -/
theorem paperFullTailLaw_terminal_map
    {A : Type*} [Fintype A] [MeasurableSpace A] [MeasurableSingletonClass A]
    (z : ℕ → Point) (d M : ℕ) (g0 : ℝ) (b : A → ℕ) (k : ℕ)
    (ν : Measure (PairedWalkSource A (paperScheduleWindow d M g0) k))
    [IsProbabilityMeasure ν] :
    (paperFullTailLaw z d M g0 b k ν).map (paperFullTailTerminalTime d M g0 b k) =
      smoothedTimeLaw
        (pairedWalkTailLaw z (paperScheduleWindow d M g0) b k ν
          ((paperScheduleList d M g0).length - k))
        (pairedWalkTime (paperScheduleWindow d M g0) b
          (k + ((paperScheduleList d M g0).length - k)))
        (terminalSmoothingLength (paperScheduleMaxT d M)) := rfl

/-- Instantiate the dyadic upper budget on the ACTUAL full-tail terminal
pushforward used by every same-family lower rate. -/
theorem paperFullTailLaw_dyadic_information_budget
    {A G : Type*} [Fintype A] [MeasurableSpace A] [MeasurableSingletonClass A]
    [Fintype G] [AddCommGroup G] [MeasurableSpace G] [MeasurableSingletonClass G]
    [MeasurableSpace Bool] [MeasurableSingletonClass Bool]
    (z : ℕ → Point) (d M R : ℕ) (hd : 1 ≤ d) (g0 : ℝ) (b : A → ℕ) (k : ℕ)
    (ν : Measure (PairedWalkSource A (paperScheduleWindow d M g0) k)) [IsProbabilityMeasure ν]
    (hstep : ∀ t, sqDist (z (t + 1)) (z t) ≤ (R : ℤ))
    (φ : ℕ → Point →+ G) (level : ℕ → ℕ) (hlevel : Monotone level) (n : ℕ)
    (hlast : ((2 ^ level n : ℕ) : ℝ) ≤ paperScheduleMaxT d M) :
    (∑ i ∈ Finset.range (n + 1),
      condMutualInfo (fun t => φ i (z t)) (wordAt (walkLetters z R hstep) (2 ^ level i))
        (observationHistory (fun j t => φ j (z t)) i)
        ((paperFullTailLaw z d M g0 b k ν).map (paperFullTailTerminalTime d M g0 b k)) /
          (2 ^ level i : ℕ)) ≤
      2 * Real.log (2 * (R + 1) + 1 : ℕ) +
        n * ((1 + 9 * Real.log (paperScheduleMaxT d M) +
          2 * Real.log (2 * (R + 1) + 1 : ℕ)) / (paperScheduleMaxT d M) ^ 9) := by
  rw [paperFullTailLaw_terminal_map]
  have hT : 1 ≤ paperScheduleMaxT d M := by
    unfold paperScheduleMaxT
    exact Real.one_le_exp (by have h := (paperScheduleX_pos d M hd).le; positivity)
  exact smoothedTimeLaw_walk_dyadic_budget _ _ z R hstep φ level hlevel n _ hT hlast

end BinaryFormMoat.GeometryIntegration
#print axioms BinaryFormMoat.GeometryIntegration.paperFullTailLaw_terminal_map
#print axioms BinaryFormMoat.GeometryIntegration.paperFullTailLaw_dyadic_information_budget
