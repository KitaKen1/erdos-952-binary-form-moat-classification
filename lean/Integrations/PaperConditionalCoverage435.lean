import Integrations.PairedWalkTerminalRestartAt435

noncomputable section
namespace BinaryFormMoat.GeometryIntegration
open EntropyIntegration MeasureTheory ProbabilityTheory
variable {A : Type*} [Fintype A] [MeasurableSpace A] [MeasurableSingletonClass A]

/-- The paper's full common terminal experiment, conditioned on its ORIGINAL
next natural time, has exactly the fresh tail's terminal-time distribution. -/
theorem paperFullTailLaw_cond_next_time_identDistrib (z : ℕ → Point) (d M : ℕ) (g0 : ℝ)
    (b : A → ℕ) (k q : ℕ) (hkq : k ≤ q) (hq : q ≤ (paperScheduleList d M g0).length)
    (ν : Measure (PairedWalkSource A (paperScheduleWindow d M g0) k)) [IsProbabilityMeasure ν]
    (c : ℕ) :
    IdentDistrib (paperFullTailTerminalTime d M g0 b k) (paperFullTailTerminalTime d M g0 b q)
      ((paperFullTailLaw z d M g0 b k ν)[|paperFullTailCheckpointTime d M g0 b k q hq ⁻¹' {c}])
      (paperFullTailLaw z d M g0 b q ((pairedWalkPrefixLaw z (paperScheduleWindow d M g0) b k q hkq ν)[|
        pairedWalkTime (paperScheduleWindow d M g0) b q ⁻¹' {c}])) := by
  let : NeZero (terminalSmoothingLength (paperScheduleMaxT d M)) := ⟨(terminalSmoothingLength_pos _).ne'⟩
  exact pairedWalkTailTerminalTime_cond_restart_at_identDistrib z (paperScheduleWindow d M g0) b
    k q (paperScheduleList d M g0).length hkq hq ν (terminalSmoothingLength (paperScheduleMaxT d M)) c

theorem paperFullTailLaw_next_time_mass (z : ℕ → Point) (d M : ℕ) (g0 : ℝ)
    (b : A → ℕ) (k q : ℕ) (hkq : k ≤ q) (hq : q ≤ (paperScheduleList d M g0).length)
    (ν : Measure (PairedWalkSource A (paperScheduleWindow d M g0) k)) (c : ℕ) :
    paperFullTailLaw z d M g0 b k ν (paperFullTailCheckpointTime d M g0 b k q hq ⁻¹' {c}) =
      pairedWalkPrefixLaw z (paperScheduleWindow d M g0) b k q hkq ν
        (pairedWalkTime (paperScheduleWindow d M g0) b q ⁻¹' {c}) := by
  let : NeZero (terminalSmoothingLength (paperScheduleMaxT d M)) := ⟨(terminalSmoothingLength_pos _).ne'⟩
  exact pairedWalkTailTerminalLaw_prefix_time_mass z (paperScheduleWindow d M g0) b
    k q (paperScheduleList d M g0).length hkq hq ν (terminalSmoothingLength (paperScheduleMaxT d M)) c

/-- Only original positive fibers receive a probability instance. -/
theorem paperFullTailLaw_cond_next_time_probability (z : ℕ → Point) (d M : ℕ) (g0 : ℝ)
    (b : A → ℕ) (k q : ℕ) (hkq : k ≤ q) (hq : q ≤ (paperScheduleList d M g0).length)
    (ν : Measure (PairedWalkSource A (paperScheduleWindow d M g0) k)) [IsProbabilityMeasure ν]
    (c : ℕ) (hc : paperFullTailLaw z d M g0 b k ν
      (paperFullTailCheckpointTime d M g0 b k q hq ⁻¹' {c}) ≠ 0) :
    IsProbabilityMeasure ((pairedWalkPrefixLaw z (paperScheduleWindow d M g0) b k q hkq ν)[|
      pairedWalkTime (paperScheduleWindow d M g0) b q ⁻¹' {c}]) := by
  rw [paperFullTailLaw_next_time_mass z d M g0 b k q hkq hq ν c] at hc
  exact cond_isProbabilityMeasure hc

/-- The ACTUAL deficient-coordinate set on the original conditioned terminal
law is exactly that on the restarted conditional tail. Root/residue alphabets
and thresholds are untouched. The equality includes zero fibers. -/
theorem paperFullTailLaw_cond_next_time_deficientCoordinates {C : Type*} [Fintype C]
    (z : ℕ → Point) (d M : ℕ) (g0 : ℝ) (b : A → ℕ) (k q : ℕ)
    (hkq : k ≤ q) (hq : q ≤ (paperScheduleList d M g0).length)
    (ν : Measure (PairedWalkSource A (paperScheduleWindow d M g0) k)) [IsProbabilityMeasure ν]
    (c : ℕ) (G : C → Type*) [∀ c, Fintype (G c)] [∀ c, MeasurableSpace (G c)]
    [∀ c, MeasurableSingletonClass (G c)] (φ : ∀ c, ℕ → G c) (τ β : ℝ) :
    deficientCoordinates ((paperFullTailLaw z d M g0 b k ν)[|
      paperFullTailCheckpointTime d M g0 b k q hq ⁻¹' {c}]) G
      (fun a ω => φ a (paperFullTailTerminalTime d M g0 b k ω)) τ β =
        deficientCoordinates (paperFullTailLaw z d M g0 b q
          ((pairedWalkPrefixLaw z (paperScheduleWindow d M g0) b k q hkq ν)[|
            pairedWalkTime (paperScheduleWindow d M g0) b q ⁻¹' {c}])) G
          (fun a ω => φ a (paperFullTailTerminalTime d M g0 b q ω)) τ β := by
  apply deficientCoordinates_eq_of_identDistrib
  intro a
  exact (paperFullTailLaw_cond_next_time_identDistrib z d M g0 b k q hkq hq ν c).comp
    (measurable_of_countable (φ a))

end BinaryFormMoat.GeometryIntegration
#print axioms BinaryFormMoat.GeometryIntegration.paperFullTailLaw_cond_next_time_identDistrib
#print axioms BinaryFormMoat.GeometryIntegration.paperFullTailLaw_next_time_mass
#print axioms BinaryFormMoat.GeometryIntegration.paperFullTailLaw_cond_next_time_probability
#print axioms BinaryFormMoat.GeometryIntegration.paperFullTailLaw_cond_next_time_deficientCoordinates
