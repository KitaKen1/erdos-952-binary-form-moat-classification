import Integrations.PairedWalkTail435
import Integrations.PaperTerminalBlock435

noncomputable section
namespace BinaryFormMoat.GeometryIntegration
open EntropyIntegration MeasureTheory ProbabilityTheory

abbrev PairedWalkTailTerminalSource (A : Type*) (N : ℕ → ℕ) (k r L : ℕ) :=
  PairedWalkSource A N (k + r) × Fin L

variable {A : Type*} [Fintype A] [MeasurableSpace A] [MeasurableSingletonClass A]

/-- One remaining-schedule experiment, followed by its independent terminal offset. -/
def pairedWalkTailTerminalLaw (z : ℕ → Point) (N : ℕ → ℕ) (b : A → ℕ) (k : ℕ)
    (ν : Measure (PairedWalkSource A N k)) (r L : ℕ) :
    Measure (PairedWalkTailTerminalSource A N k r L) :=
  (pairedWalkTailLaw z N b k ν r).prod (uniformOn (Set.univ : Set (Fin L)))

instance pairedWalkTailTerminalLaw_isProbabilityMeasure (z : ℕ → Point) (N : ℕ → ℕ)
    (b : A → ℕ) (k : ℕ) (ν : Measure (PairedWalkSource A N k)) [IsProbabilityMeasure ν]
    (r L : ℕ) [NeZero L] : IsProbabilityMeasure (pairedWalkTailTerminalLaw z N b k ν r L) := by
  unfold pairedWalkTailTerminalLaw
  infer_instance

def pairedWalkTailTerminalTime (N : ℕ → ℕ) (b : A → ℕ) (k r L : ℕ)
    (ω : PairedWalkTailTerminalSource A N k r L) : ℕ := pairedWalkTime N b (k + r) ω.1 + ω.2.val

def pairedWalkTailCheckpoint (N : ℕ → ℕ) (k r L j : ℕ) (hj : j ≤ r)
    (ω : PairedWalkTailTerminalSource A N k r L) : PairedWalkSource A N (k + j) :=
  pairedWalkCheckpoint N (k + r) ⟨k + j, by omega⟩ ω.1

/-- Intermediate exact marginal, including the fresh terminal offset. -/
theorem pairedWalkTailTerminalLaw_checkpoint_map (z : ℕ → Point) (N : ℕ → ℕ)
    (b : A → ℕ) (k : ℕ) (ν : Measure (PairedWalkSource A N k)) (r L j : ℕ)
    [NeZero L] (hj : j ≤ r) :
    (pairedWalkTailTerminalLaw z N b k ν r L).map (pairedWalkTailCheckpoint N k r L j hj) =
      pairedWalkTailLaw z N b k ν j := by
  change ((pairedWalkTailLaw z N b k ν r).prod _).map
    (pairedWalkCheckpoint N (k + r) ⟨k + j, by omega⟩ ∘ Prod.fst) = _
  rw [← Measure.map_map (measurable_of_finite _) measurable_fst, Measure.map_fst_prod,
    measure_univ, one_smul]
  exact pairedWalkTailLaw_checkpoint_map z N b k ν r j hj

theorem pairedWalkTailTerminalLaw_checkpoint_identDistrib {S : Type*} [MeasurableSpace S]
    (z : ℕ → Point) (N : ℕ → ℕ) (b : A → ℕ) (k : ℕ)
    (ν : Measure (PairedWalkSource A N k)) (r L j : ℕ) [NeZero L] (hj : j ≤ r)
    (F : PairedWalkSource A N (k + j) → S) :
    IdentDistrib (fun ω => F (pairedWalkTailCheckpoint N k r L j hj ω)) F
      (pairedWalkTailTerminalLaw z N b k ν r L) (pairedWalkTailLaw z N b k ν j) := by
  refine ⟨(measurable_of_finite _).aemeasurable, (measurable_of_finite _).aemeasurable, ?_⟩
  change (pairedWalkTailTerminalLaw z N b k ν r L).map (F ∘ pairedWalkTailCheckpoint N k r L j hj) = _
  rw [← Measure.map_map (measurable_of_finite _) (measurable_of_finite _),
    pairedWalkTailTerminalLaw_checkpoint_map]

/-- Conditional subset/label entropies are exactly those of the tail's marginal.
Instantiate the base law with any positive earlier conditional law. -/
theorem pairedWalkTailTerminalLaw_checkpoint_jointEntropy {ι Q : Type*} [Fintype ι] [Fintype Q]
    (z : ℕ → Point) (N : ℕ → ℕ) (b : A → ℕ) (k : ℕ)
    (ν : Measure (PairedWalkSource A N k)) (r L j : ℕ) [NeZero L] (hj : j ≤ r)
    (G : ι × Q → Type*) [∀ c, MeasurableSpace (G c)] (φ : ∀ c, Point → G c) (s : ℕ) :
    labelSubsetJointEntropy (pairedWalkTailTerminalLaw z N b k ν r L) G
      (fun c ω => φ c (z (pairedWalkTime N b (k + j) (pairedWalkTailCheckpoint N k r L j hj ω)))) s =
    labelSubsetJointEntropy (pairedWalkTailLaw z N b k ν j) G
      (fun c ω => φ c (z (pairedWalkTime N b (k + j) ω))) s := by
  unfold labelSubsetJointEntropy
  congr 1
  funext S ρ
  exact (pairedWalkTailTerminalLaw_checkpoint_identDistrib z N b k ν r L j hj
    (fun ω (i : S) => φ (i.1, ρ i.1) (z (pairedWalkTime N b (k + j) ω)))).entropy_congr

/-- Conditioning on the initial checkpoint leaves every remaining pair/coin
and the terminal offset fresh. This identity includes zero fibers. -/
theorem pairedWalkTailTerminalLaw_cond_checkpoint (z : ℕ → Point) (N : ℕ → ℕ)
    (b : A → ℕ) (k : ℕ) (ν : Measure (PairedWalkSource A N k)) [IsProbabilityMeasure ν]
    (r L : ℕ) [NeZero L] {B : Type*} [MeasurableSpace B] [MeasurableSingletonClass B]
    (V : PairedWalkSource A N k → B) (c : B) :
    (pairedWalkTailTerminalLaw z N b k ν r L)[|
      (fun ω => V (pairedWalkPast N k r ω.1)) ⁻¹' {c}] =
      pairedWalkTailTerminalLaw z N b k (ν[|V ⁻¹' {c}]) r L := by
  unfold pairedWalkTailTerminalLaw
  rw [independentOffset_cond_checkpoint (pairedWalkTailLaw z N b k ν r)
    (fun ω => V (pairedWalkPast N k r ω)) L c, pairedWalkTailLaw_cond_checkpoint]

omit [Fintype A] [MeasurableSpace A] [MeasurableSingletonClass A] in
/-- A singleton offset is exactly the original later checkpoint time. -/
theorem pairedWalkTailTerminalTime_one (N : ℕ → ℕ) (b : A → ℕ) (k r : ℕ) :
    pairedWalkTailTerminalTime (A := A) N b k r 1 =
      (fun ω => pairedWalkTime N b (k + r) (pairedWalkTailCheckpoint N k r 1 r le_rfl ω)) := by
  funext ω
  have h0 : ω.2.val = 0 := by have h := ω.2.isLt; omega
  dsimp [pairedWalkTailTerminalTime, pairedWalkTailCheckpoint]
  rw [pairedWalkCheckpoint_self]
  simp only [h0, Nat.add_zero, id_eq]

omit [Fintype A] [MeasurableSpace A] [MeasurableSingletonClass A] in
/-- Deterministic physical budget for any remaining prefix ending by the common
terminal checkpoint. It applies under ALL starting and conditional laws. -/
theorem paperTailTerminalTime_checkpoint_bounds (b : A → ℕ) (d M : ℕ) (g0 : ℝ)
    (k r L j : ℕ) (hL : L ≤ terminalSmoothingLength (paperScheduleMaxT d M)) (hj : j ≤ r) (hend : k + r ≤ (paperScheduleList d M g0).length)
    (hop : k + j < (paperScheduleList d M g0).length)
    (ω : PairedWalkTailTerminalSource A (paperScheduleWindow d M g0) k r L) :
    pairedWalkTime (paperScheduleWindow d M g0) b (k + j)
        (pairedWalkTailCheckpoint _ k r L j hj ω) ≤ pairedWalkTailTerminalTime _ b k r L ω ∧
      pairedWalkTailTerminalTime _ b k r L ω ≤
        pairedWalkTime (paperScheduleWindow d M g0) b (k + j)
          (pairedWalkTailCheckpoint _ k r L j hj ω) +
            paperFutureShift ((paperScheduleList d M g0).get ⟨k + j, hop⟩) := by
  have ht := pairedWalkCheckpoint_time_bounds (paperScheduleWindow d M g0) b
    (k + r) ⟨k + j, by omega⟩ ω.1
  have hs := paperScheduleWindow_suffix_sum_le d M g0 ⟨k + j, hop⟩
    (k + r - (k + j)) (by dsimp; omega)
  have ho : ω.2.val ≤ terminalSmoothingLength (paperScheduleMaxT d M) - 1 := by
    have h := ω.2.isLt
    omega
  dsimp [pairedWalkTailCheckpoint, pairedWalkTailTerminalTime]
  unfold paperFutureShift
  dsimp only at ht
  simp only [List.get_eq_getElem] at hs
  constructor <;> omega

/-- The same displacement alphabet budget as the full experiment, at any tail
checkpoint. The measure is arbitrary, so positive fibers require no new threshold. -/
theorem paperTailCheckpoint_displacement_entropy_budget (z : ℕ → Point) (b : A → ℕ)
    (d M R : ℕ) (g0 : ℝ) (hstep : ∀ t, sqDist (z (t + 1)) (z t) ≤ (R : ℤ))
    (k r L j : ℕ) (hL : L ≤ terminalSmoothingLength (paperScheduleMaxT d M)) (hj : j ≤ r) (hend : k + r ≤ (paperScheduleList d M g0).length)
    (hop : k + j < (paperScheduleList d M g0).length)
    (ν : Measure (PairedWalkTailTerminalSource A (paperScheduleWindow d M g0) k r L))
    (hlog : Real.log (paperFutureShift ((paperScheduleList d M g0).get ⟨k + j, hop⟩) + 1 : ℕ) ≤
      2 * (paperOpG ((paperScheduleList d M g0).get ⟨k + j, hop⟩) *
        paperOpU ((paperScheduleList d M g0).get ⟨k + j, hop⟩))) :
    entropy (fun ω => z (pairedWalkTailTerminalTime _ b k r L ω) -
      z (pairedWalkTime (paperScheduleWindow d M g0) b (k + j)
        (pairedWalkTailCheckpoint _ k r L j hj ω))) ν ≤
      4 * (paperOpG ((paperScheduleList d M g0).get ⟨k + j, hop⟩) *
        paperOpU ((paperScheduleList d M g0).get ⟨k + j, hop⟩)) +
          2 * Real.log (2 * (R + 1) + 1 : ℕ) := by
  let S := paperFutureShift ((paperScheduleList d M g0).get ⟨k + j, hop⟩)
  have hm (ω : PairedWalkTailTerminalSource A (paperScheduleWindow d M g0) k r L) :
      z (pairedWalkTailTerminalTime _ b k r L ω) -
        z (pairedWalkTime (paperScheduleWindow d M g0) b (k + j)
          (pairedWalkTailCheckpoint _ k r L j hj ω)) ∈ displacementBox ((R + 1) * S) := by
    have ht := paperTailTerminalTime_checkpoint_bounds b d M g0 k r L j hL hj hend hop ω
    exact walk_displacement_mem z (R + 1) (sqDist_walk_coordinate_steps z R hstep)
      _ _ _ ht.1 ht.2
  have h := entropy_le_log_card_of_mem (A := displacementBox ((R + 1) * S))
    (measurable_of_finite _) (ae_of_all ν hm)
  have he : entropy (fun ω => z (pairedWalkTailTerminalTime _ b k r L ω) -
      z (pairedWalkTime (paperScheduleWindow d M g0) b (k + j)
        (pairedWalkTailCheckpoint _ k r L j hj ω))) ν ≤
        2 * Real.log (2 * ((R + 1) * S) + 1 : ℕ) := by
    simpa only [displacementBox_card, Nat.cast_pow, Real.log_pow, Nat.cast_ofNat] using h
  exact he.trans (paperFutureShift_displacement_log_bound _ R hlog)

/-- One physical displacement cost transports a joint subset entropy on the
actual tail law. No entropy premise on the terminal law is introduced. -/
theorem paperTailCheckpoint_jointEntropy_budget {ι Q : Type*}
    [Fintype ι] [Fintype Q] [Nonempty Q]
    (z : ℕ → Point) (b : A → ℕ) (d M R : ℕ) (g0 : ℝ)
    (hstep : ∀ t, sqDist (z (t + 1)) (z t) ≤ (R : ℤ))
    (k : ℕ) (ν : Measure (PairedWalkSource A (paperScheduleWindow d M g0) k))
    [IsProbabilityMeasure ν] (r L j : ℕ) [NeZero L]
    (hL : L ≤ terminalSmoothingLength (paperScheduleMaxT d M)) (hj : j ≤ r)
    (hend : k + r ≤ (paperScheduleList d M g0).length)
    (hop : k + j < (paperScheduleList d M g0).length)
    (G : ι × Q → Type*) [∀ c, Fintype (G c)] [∀ c, MeasurableSpace (G c)]
    [∀ c, MeasurableSingletonClass (G c)] [∀ c, AddCommGroup (G c)]
    (φ : ∀ c, Point →+ G c) (s : ℕ) (hs : s ≤ Fintype.card ι)
    (hlog : Real.log (paperFutureShift ((paperScheduleList d M g0).get ⟨k + j, hop⟩) + 1 : ℕ) ≤
      2 * (paperOpG ((paperScheduleList d M g0).get ⟨k + j, hop⟩) *
        paperOpU ((paperScheduleList d M g0).get ⟨k + j, hop⟩))) :
    labelSubsetJointEntropy (pairedWalkTailLaw z (paperScheduleWindow d M g0) b k ν j) G
      (fun c ω => φ c (z (pairedWalkTime (paperScheduleWindow d M g0) b (k + j) ω))) s -
        (4 * (paperOpG ((paperScheduleList d M g0).get ⟨k + j, hop⟩) *
          paperOpU ((paperScheduleList d M g0).get ⟨k + j, hop⟩)) +
            2 * Real.log (2 * (R + 1) + 1 : ℕ)) ≤
      labelSubsetJointEntropy (pairedWalkTailTerminalLaw z (paperScheduleWindow d M g0) b k ν r L) G
        (fun c ω => φ c (z (pairedWalkTailTerminalTime _ b k r L ω))) s := by
  have hl := labelSubsetJointEntropy_loss_le_displacement
    (pairedWalkTailTerminalLaw z (paperScheduleWindow d M g0) b k ν r L) G
    (fun c ω => φ c (z (pairedWalkTime (paperScheduleWindow d M g0) b (k + j)
      (pairedWalkTailCheckpoint _ k r L j hj ω))))
    (fun c ω => φ c (z (pairedWalkTailTerminalTime _ b k r L ω)))
    (fun ω => z (pairedWalkTailTerminalTime _ b k r L ω) -
      z (pairedWalkTime (paperScheduleWindow d M g0) b (k + j)
        (pairedWalkTailCheckpoint _ k r L j hj ω)))
    (fun c => φ c) (by intro c ω; rw [map_sub]; abel) s hs
  rw [pairedWalkTailTerminalLaw_checkpoint_jointEntropy] at hl
  have hu := paperTailCheckpoint_displacement_entropy_budget z b d M R g0 hstep k r L j hL hj hend hop
    (pairedWalkTailTerminalLaw z (paperScheduleWindow d M g0) b k ν r L) hlog
  linarith

/-- Transport to an actual intermediate checkpoint, with NO smoothing at
that checkpoint. This is the high-entropy input for the next coverage stage. -/
theorem paperTailCheckpoint_jointEntropy_later {ι Q : Type*}
    [Fintype ι] [Fintype Q] [Nonempty Q]
    (z : ℕ → Point) (b : A → ℕ) (d M R : ℕ) (g0 : ℝ)
    (hstep : ∀ t, sqDist (z (t + 1)) (z t) ≤ (R : ℤ))
    (k : ℕ) (ν : Measure (PairedWalkSource A (paperScheduleWindow d M g0) k))
    [IsProbabilityMeasure ν] (r j : ℕ) (hj : j ≤ r)
    (hend : k + r ≤ (paperScheduleList d M g0).length)
    (hop : k + j < (paperScheduleList d M g0).length)
    (G : ι × Q → Type*) [∀ c, Fintype (G c)] [∀ c, MeasurableSpace (G c)]
    [∀ c, MeasurableSingletonClass (G c)] [∀ c, AddCommGroup (G c)]
    (φ : ∀ c, Point →+ G c) (s : ℕ) (hs : s ≤ Fintype.card ι)
    (hlog : Real.log (paperFutureShift ((paperScheduleList d M g0).get ⟨k + j, hop⟩) + 1 : ℕ) ≤
      2 * (paperOpG ((paperScheduleList d M g0).get ⟨k + j, hop⟩) *
        paperOpU ((paperScheduleList d M g0).get ⟨k + j, hop⟩))) :
    labelSubsetJointEntropy (pairedWalkTailLaw z (paperScheduleWindow d M g0) b k ν j) G
      (fun c ω => φ c (z (pairedWalkTime (paperScheduleWindow d M g0) b (k + j) ω))) s -
        (4 * (paperOpG ((paperScheduleList d M g0).get ⟨k + j, hop⟩) *
          paperOpU ((paperScheduleList d M g0).get ⟨k + j, hop⟩)) +
            2 * Real.log (2 * (R + 1) + 1 : ℕ)) ≤
      labelSubsetJointEntropy (pairedWalkTailLaw z (paperScheduleWindow d M g0) b k ν r) G
        (fun c ω => φ c (z (pairedWalkTime (paperScheduleWindow d M g0) b (k + r) ω))) s := by
  have h := paperTailCheckpoint_jointEntropy_budget z b d M R g0 hstep k ν r 1 j
    (terminalSmoothingLength_pos _ ) hj hend hop G φ s hs hlog
  rw [pairedWalkTailTerminalTime_one, pairedWalkTailTerminalLaw_checkpoint_jointEntropy] at h
  exact h

end BinaryFormMoat.GeometryIntegration

#print axioms BinaryFormMoat.GeometryIntegration.PairedWalkTailTerminalSource
#print axioms BinaryFormMoat.GeometryIntegration.pairedWalkTailTerminalLaw
#print axioms BinaryFormMoat.GeometryIntegration.pairedWalkTailTerminalLaw_isProbabilityMeasure
#print axioms BinaryFormMoat.GeometryIntegration.pairedWalkTailTerminalTime
#print axioms BinaryFormMoat.GeometryIntegration.pairedWalkTailCheckpoint
#print axioms BinaryFormMoat.GeometryIntegration.pairedWalkTailTerminalLaw_checkpoint_map
#print axioms BinaryFormMoat.GeometryIntegration.pairedWalkTailTerminalLaw_checkpoint_identDistrib
#print axioms BinaryFormMoat.GeometryIntegration.pairedWalkTailTerminalLaw_checkpoint_jointEntropy
#print axioms BinaryFormMoat.GeometryIntegration.pairedWalkTailTerminalLaw_cond_checkpoint
#print axioms BinaryFormMoat.GeometryIntegration.paperTailTerminalTime_checkpoint_bounds
#print axioms BinaryFormMoat.GeometryIntegration.paperTailCheckpoint_displacement_entropy_budget
#print axioms BinaryFormMoat.GeometryIntegration.paperTailCheckpoint_jointEntropy_budget

#print axioms BinaryFormMoat.GeometryIntegration.pairedWalkTailTerminalTime_one
#print axioms BinaryFormMoat.GeometryIntegration.paperTailCheckpoint_jointEntropy_later
