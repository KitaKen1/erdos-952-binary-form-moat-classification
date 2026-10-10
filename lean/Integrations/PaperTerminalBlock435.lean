import Integrations.PaperGlobalBlock435
import Integrations.PaperCheckpointEntropy435

noncomputable section
open scoped Classical
namespace BinaryFormMoat.GeometryIntegration
open EntropyIntegration MeasureTheory ProbabilityTheory

theorem labelledPointEntropyMean_eq_joint {Ω ι Q : Type*}
    [MeasurableSpace Ω] [Fintype ι] [DecidableEq ι] [Fintype Q]
    (K : ι → Type*) [∀ i, AddCommGroup (K i)] [∀ i, Fintype (K i)]
    [∀ i, MeasurableSpace (K i)] [∀ i, MeasurableSingletonClass (K i)]
    (F : ∀ i, Q → Point →+ K i) (μ : Measure Ω) (s : ℕ) (X : Ω → Point) :
    labelledPointEntropyMean K F μ s X =
      labelSubsetJointEntropy μ (fun c : ι × Q => K c.1) (fun c ω => F c.1 c.2 (X ω)) s := rfl

/-- The SAME recorded scale pays its entire future displacement. The fixed
step-alphabet constant is absorbed by the existing paper size criterion. -/
theorem paper_terminal_relative_cost (f : Polynomial ℤ) (R : ℕ) (U L g : ℝ)
    (hU : 0 < U) (hL : 0 < L) (hL2 : Real.log 2 ≤ L)
    (hg : 0 < g) (hg64 : g < 1 / 64)
    (hsize : paperEnrichmentSizeConstant f (R + 1) * L ≤ g ^ 10 * U) :
    0 < paperInputRank U L ∧ U / 2 ≤ (paperInputRank U L : ℝ) * L ∧
      4 * (g * U) + 2 * Real.log (2 * (R + 1) + 1 : ℕ) ≤
        (10 * g) * ((paperInputRank U L : ℝ) * L) := by
  have hs := paperEnrichment_size_inputs f (R + 1) U L g hU hL hL2 hg (by linarith) hsize
  have hr := paperRank_pair_bounds U L g hU hL hg hg64 hs.2.1
  have hg2 : g ^ 2 ≤ g := by nlinarith
  have hghalf : g ^ 2 ≤ 1 / 2 := by nlinarith
  have hmean := mul_le_mul_of_nonneg_right hghalf hU.le
  have hmass : U / 2 ≤ (paperInputRank U L : ℝ) * L := by linarith [hr.2.2.2]
  have hcost : 2 * Real.log (2 * (R + 1) + 1 : ℕ) ≤ g * U := by
    have hlog : Real.log (2 * (R + 1) + 1 : ℕ) ≤ Real.log (4 * (R + 1) + 1 : ℕ) :=
      Real.log_le_log (by positivity) (by exact_mod_cast (by omega : 2 * (R + 1) + 1 ≤ 4 * (R + 1) + 1))
    have hK := (paperEnrichmentFixedCost_bounds f (R + 1)).2.2.2.2
    exact (mul_le_mul_of_nonneg_left hlog (by norm_num)).trans
      (hK.trans (hs.1.trans (mul_le_mul_of_nonneg_right hg2 hU.le)))
  refine ⟨by omega, hmass, ?_⟩
  nlinarith [mul_le_mul_of_nonneg_left hmass (show 0 ≤ 10 * g by positivity)]

theorem paperCheckpoint_labelledPoint_entropy_transport
    {A ι Q : Type*} [Fintype A] [MeasurableSpace A] [MeasurableSingletonClass A]
    [Fintype ι] [DecidableEq ι] [Fintype Q] [Nonempty Q]
    (K : ι → Type*) [∀ i, AddCommGroup (K i)] [∀ i, Fintype (K i)]
    [∀ i, MeasurableSpace (K i)] [∀ i, MeasurableSingletonClass (K i)]
    (F : ∀ i, Q → Point →+ K i)
    (z : ℕ → Point) (μ : Measure A) [IsProbabilityMeasure μ] (a : A → ℕ)
    (d M R : ℕ) (g0 : ℝ) (hstep : ∀ t, sqDist (z (t + 1)) (z t) ≤ (R : ℤ))
    (k : Fin (paperScheduleList d M g0).length) (s : ℕ) (hs : s ≤ Fintype.card ι)
    (hlog : Real.log (paperFutureShift ((paperScheduleList d M g0).get k) + 1 : ℕ) ≤
      2 * (paperOpG ((paperScheduleList d M g0).get k) * paperOpU ((paperScheduleList d M g0).get k))) :
    labelledPointEntropyMean K F (pairedWalkLaw z (paperScheduleWindow d M g0) μ a k.val) s
      (fun ω => z (pairedWalkTime (paperScheduleWindow d M g0) a k.val ω)) -
        (4 * (paperOpG ((paperScheduleList d M g0).get k) * paperOpU ((paperScheduleList d M g0).get k)) +
          2 * Real.log (2 * (R + 1) + 1 : ℕ)) ≤
      labelledPointEntropyMean K F (paperTerminalLaw z μ a d M g0) s
        (fun ω => z (paperTerminalTime a d M g0 ω)) :=
  paperCheckpoint_jointEntropy_budget z a d M g0 R hstep k μ
    (fun c : ι × Q => K c.1) (fun c => F c.1 c.2) s hs hlog

/-- A proved checkpoint lower bound transfers to the actual terminal law
with at most 10g extra normalized deficit. No terminal lower bound is assumed. -/
theorem paperCheckpoint_labelledPoint_normalized_terminal
    {A Q : Type*} [Fintype A] [MeasurableSpace A] [MeasurableSingletonClass A]
    [Fintype Q] [Nonempty Q]
    (f : Polynomial ℤ) (P : Finset ℕ) [∀ p : P, NeZero p.val]
    (S : (p : ℕ) → Finset (ZMod p)) (e : ∀ p : P, Q ≃ S p.val)
    (z : ℕ → Point) (μ : Measure A) [IsProbabilityMeasure μ] (a : A → ℕ)
    (M R : ℕ) (g0 : ℝ) (hstep : ∀ t, sqDist (z (t + 1)) (z t) ≤ (R : ℤ))
    (k : Fin (paperScheduleList f.natDegree M g0).length) (U g δ : ℝ)
    (hU : 0 < U) (hg : 0 < g) (hg64 : g < 1 / 64)
    (hL : 0 < primeBatchLogMean P) (hL2 : Real.log 2 ≤ primeBatchLogMean P)
    (hget : paperOpU ((paperScheduleList f.natDegree M g0).get k) = U ∧
      paperOpG ((paperScheduleList f.natDegree M g0).get k) = g)
    (hsize : paperEnrichmentSizeConstant f (R + 1) * primeBatchLogMean P ≤ g ^ 10 * U)
    (hinventory : paperInputRank U (primeBatchLogMean P) ≤ P.card)
    (hlog : Real.log (paperFutureShift ((paperScheduleList f.natDegree M g0).get k) + 1 : ℕ) ≤
      2 * (paperOpG ((paperScheduleList f.natDegree M g0).get k) * paperOpU ((paperScheduleList f.natDegree M g0).get k)))
    (hhigh : 1 - δ ≤
      labelledPointEntropyMean (fun p : P => ZMod p.val) (labelledPrimeResidue P S e)
        (pairedWalkLaw z (paperScheduleWindow f.natDegree M g0) μ a k.val)
        (paperInputRank U (primeBatchLogMean P))
        (fun ω => z (pairedWalkTime (paperScheduleWindow f.natDegree M g0) a k.val ω)) /
        ((paperInputRank U (primeBatchLogMean P) : ℝ) * primeBatchLogMean P)) :
    1 - δ - 10 * g ≤
      labelledPointEntropyMean (fun p : P => ZMod p.val) (labelledPrimeResidue P S e)
        (paperTerminalLaw z μ a f.natDegree M g0) (paperInputRank U (primeBatchLogMean P))
        (fun ω => z (paperTerminalTime a f.natDegree M g0 ω)) /
        ((paperInputRank U (primeBatchLogMean P) : ℝ) * primeBatchLogMean P) := by
  have hc := paper_terminal_relative_cost f R U (primeBatchLogMean P) g hU hL hL2 hg hg64 hsize
  have hm : 0 < (paperInputRank U (primeBatchLogMean P) : ℝ) * primeBatchLogMean P := by
    exact mul_pos (by exact_mod_cast hc.1) hL
  have ht := paperCheckpoint_labelledPoint_entropy_transport (fun p : P => ZMod p.val)
    (labelledPrimeResidue P S e) z μ a f.natDegree M R g0 hstep k
    (paperInputRank U (primeBatchLogMean P)) (by simpa using hinventory) hlog
  rw [hget.1, hget.2] at ht
  apply (le_div_iff₀ hm).mpr
  have hh := (le_div_iff₀ hm).mp hhigh
  nlinarith [hc.2.2]

end BinaryFormMoat.GeometryIntegration

#print axioms BinaryFormMoat.GeometryIntegration.labelledPointEntropyMean_eq_joint
#print axioms BinaryFormMoat.GeometryIntegration.paper_terminal_relative_cost
#print axioms BinaryFormMoat.GeometryIntegration.paperCheckpoint_labelledPoint_entropy_transport
#print axioms BinaryFormMoat.GeometryIntegration.paperCheckpoint_labelledPoint_normalized_terminal
