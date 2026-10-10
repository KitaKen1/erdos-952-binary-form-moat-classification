import Integrations.PaperTailHistory435
import Integrations.PaperTailEnrichment435

noncomputable section
open Filter
namespace BinaryFormMoat.GeometryIntegration
open EntropyIntegration MeasureTheory ProbabilityTheory

/-- A proved checkpoint lower bound transfers to the actual terminal law
with at most 10g extra normalized deficit. No terminal lower bound is assumed. -/
theorem paperTailCheckpoint_labelledPoint_normalized_terminal
    {A Q : Type*} [Fintype A] [MeasurableSpace A] [MeasurableSingletonClass A]
    [Fintype Q] [Nonempty Q]
    (f : Polynomial ℤ) (P : Finset ℕ) [∀ p : P, NeZero p.val]
    (S : (p : ℕ) → Finset (ZMod p)) (e : ∀ p : P, Q ≃ S p.val)
    (z : ℕ → Point) (a : A → ℕ)
    (M R : ℕ) (g0 : ℝ) (hstep : ∀ t, sqDist (z (t + 1)) (z t) ≤ (R : ℤ))
    (k : ℕ) (ν : Measure (PairedWalkSource A (paperScheduleWindow f.natDegree M g0) k))
    [IsProbabilityMeasure ν] (r j : ℕ) (hj : j ≤ r)
    (hend : k + r ≤ (paperScheduleList f.natDegree M g0).length)
    (hop : k + j < (paperScheduleList f.natDegree M g0).length) (U g δ : ℝ)
    (hU : 0 < U) (hg : 0 < g) (hg64 : g < 1 / 64)
    (hL : 0 < primeBatchLogMean P) (hL2 : Real.log 2 ≤ primeBatchLogMean P)
    (hget : paperOpU ((paperScheduleList f.natDegree M g0).get ⟨k + j, hop⟩) = U ∧
      paperOpG ((paperScheduleList f.natDegree M g0).get ⟨k + j, hop⟩) = g)
    (hsize : paperEnrichmentSizeConstant f (R + 1) * primeBatchLogMean P ≤ g ^ 10 * U)
    (hinventory : paperInputRank U (primeBatchLogMean P) ≤ P.card)
    (hlog : Real.log (paperFutureShift ((paperScheduleList f.natDegree M g0).get ⟨k + j, hop⟩) + 1 : ℕ) ≤
      2 * (paperOpG ((paperScheduleList f.natDegree M g0).get ⟨k + j, hop⟩) * paperOpU ((paperScheduleList f.natDegree M g0).get ⟨k + j, hop⟩)))
    (hhigh : 1 - δ ≤
      labelledPointEntropyMean (fun p : P => ZMod p.val) (labelledPrimeResidue P S e)
        (pairedWalkTailLaw z (paperScheduleWindow f.natDegree M g0) a k ν j)
        (paperInputRank U (primeBatchLogMean P))
        (fun ω => z (pairedWalkTime (paperScheduleWindow f.natDegree M g0) a (k + j) ω)) /
        ((paperInputRank U (primeBatchLogMean P) : ℝ) * primeBatchLogMean P)) :
    1 - δ - 10 * g ≤
      labelledPointEntropyMean (fun p : P => ZMod p.val) (labelledPrimeResidue P S e)
        (pairedWalkTailTerminalLaw z (paperScheduleWindow f.natDegree M g0) a k ν r
          (terminalSmoothingLength (paperScheduleMaxT f.natDegree M))) (paperInputRank U (primeBatchLogMean P))
        (fun ω => z (pairedWalkTailTerminalTime (paperScheduleWindow f.natDegree M g0) a k r
          (terminalSmoothingLength (paperScheduleMaxT f.natDegree M)) ω)) /
        ((paperInputRank U (primeBatchLogMean P) : ℝ) * primeBatchLogMean P) := by
  have hc := paper_terminal_relative_cost f R U (primeBatchLogMean P) g hU hL hL2 hg hg64 hsize
  have hm : 0 < (paperInputRank U (primeBatchLogMean P) : ℝ) * primeBatchLogMean P := by
    exact mul_pos (by exact_mod_cast hc.1) hL
  let : NeZero (terminalSmoothingLength (paperScheduleMaxT f.natDegree M)) :=
    ⟨(terminalSmoothingLength_pos _).ne'⟩
  have ht := paperTailCheckpoint_jointEntropy_budget z a f.natDegree M R g0 hstep k ν r (terminalSmoothingLength (paperScheduleMaxT f.natDegree M)) j
    le_rfl hj hend hop (fun c : P × Q => ZMod c.1.val)
    (fun c => labelledPrimeResidue P S e c.1 c.2)
    (paperInputRank U (primeBatchLogMean P)) (by simpa using hinventory) hlog
  rw [hget.1, hget.2] at ht
  simp only [labelledPointEntropyMean_eq_joint] at hhigh ⊢
  apply (le_div_iff₀ hm).mpr
  have hh := (le_div_iff₀ hm).mp hhigh
  nlinarith [hc.2.2]

/-- A proved checkpoint lower bound transfers to the actual later checkpoint law
with at most 10g extra normalized deficit. No later lower bound is assumed. -/
theorem paperTailCheckpoint_labelledPoint_normalized_later
    {A Q : Type*} [Fintype A] [MeasurableSpace A] [MeasurableSingletonClass A]
    [Fintype Q] [Nonempty Q]
    (f : Polynomial ℤ) (P : Finset ℕ) [∀ p : P, NeZero p.val]
    (S : (p : ℕ) → Finset (ZMod p)) (e : ∀ p : P, Q ≃ S p.val)
    (z : ℕ → Point) (a : A → ℕ)
    (M R : ℕ) (g0 : ℝ) (hstep : ∀ t, sqDist (z (t + 1)) (z t) ≤ (R : ℤ))
    (k : ℕ) (ν : Measure (PairedWalkSource A (paperScheduleWindow f.natDegree M g0) k))
    [IsProbabilityMeasure ν] (r j : ℕ) (hj : j ≤ r)
    (hend : k + r ≤ (paperScheduleList f.natDegree M g0).length)
    (hop : k + j < (paperScheduleList f.natDegree M g0).length) (U g δ : ℝ)
    (hU : 0 < U) (hg : 0 < g) (hg64 : g < 1 / 64)
    (hL : 0 < primeBatchLogMean P) (hL2 : Real.log 2 ≤ primeBatchLogMean P)
    (hget : paperOpU ((paperScheduleList f.natDegree M g0).get ⟨k + j, hop⟩) = U ∧
      paperOpG ((paperScheduleList f.natDegree M g0).get ⟨k + j, hop⟩) = g)
    (hsize : paperEnrichmentSizeConstant f (R + 1) * primeBatchLogMean P ≤ g ^ 10 * U)
    (hinventory : paperInputRank U (primeBatchLogMean P) ≤ P.card)
    (hlog : Real.log (paperFutureShift ((paperScheduleList f.natDegree M g0).get ⟨k + j, hop⟩) + 1 : ℕ) ≤
      2 * (paperOpG ((paperScheduleList f.natDegree M g0).get ⟨k + j, hop⟩) * paperOpU ((paperScheduleList f.natDegree M g0).get ⟨k + j, hop⟩)))
    (hhigh : 1 - δ ≤
      labelledPointEntropyMean (fun p : P => ZMod p.val) (labelledPrimeResidue P S e)
        (pairedWalkTailLaw z (paperScheduleWindow f.natDegree M g0) a k ν j)
        (paperInputRank U (primeBatchLogMean P))
        (fun ω => z (pairedWalkTime (paperScheduleWindow f.natDegree M g0) a (k + j) ω)) /
        ((paperInputRank U (primeBatchLogMean P) : ℝ) * primeBatchLogMean P)) :
    1 - δ - 10 * g ≤
      labelledPointEntropyMean (fun p : P => ZMod p.val) (labelledPrimeResidue P S e)
        (pairedWalkTailLaw z (paperScheduleWindow f.natDegree M g0) a k ν r) (paperInputRank U (primeBatchLogMean P))
        (fun ω => z (pairedWalkTime (paperScheduleWindow f.natDegree M g0) a (k + r) ω)) /
        ((paperInputRank U (primeBatchLogMean P) : ℝ) * primeBatchLogMean P) := by
  have hc := paper_terminal_relative_cost f R U (primeBatchLogMean P) g hU hL hL2 hg hg64 hsize
  have hm : 0 < (paperInputRank U (primeBatchLogMean P) : ℝ) * primeBatchLogMean P := by
    exact mul_pos (by exact_mod_cast hc.1) hL
  have ht := paperTailCheckpoint_jointEntropy_later z a f.natDegree M R g0 hstep k ν r j
    hj hend hop (fun c : P × Q => ZMod c.1.val)
    (fun c => labelledPrimeResidue P S e c.1 c.2)
    (paperInputRank U (primeBatchLogMean P)) (by simpa using hinventory) hlog
  rw [hget.1, hget.2] at ht
  simp only [labelledPointEntropyMean_eq_joint] at hhigh ⊢
  apply (le_div_iff₀ hm).mpr
  have hh := (le_div_iff₀ hm).mp hhigh
  nlinarith [hc.2.2]

theorem paperMiddle_preserved_deficit_bound (M : ℕ) :
    90 * paperScheduleMiddleG M + (1 / 2 : ℝ) ^ paperMiddleIterations M ≤
      91 * Real.exp (-Real.log 2 * (M : ℝ) ^ 3) := by
  have hlog : Real.log 2 ≤ 1 := (by linarith [Real.log_lt_sub_one_of_pos (by norm_num : (0 : ℝ) < 2) (by norm_num)] : _)
  have he : Real.exp (-(M : ℝ) ^ 3) ≤ Real.exp (-Real.log 2 * (M : ℝ) ^ 3) := by
    apply Real.exp_le_exp.mpr
    nlinarith [pow_nonneg (Nat.cast_nonneg M : (0 : ℝ) ≤ M) 3]
  rw [paper_half_pow_exp]
  simp only [paperMiddleIterations, Nat.cast_pow, paperScheduleMiddleG]
  linarith

/-- The middle deficit is exponentially small in M^3 with explicit c=log(2)/2. -/
theorem paperMiddle_preserved_deficit_eventually :
    ∃ M0 : ℕ, ∀ M ≥ M0,
      90 * paperScheduleMiddleG M + (1 / 2 : ℝ) ^ paperMiddleIterations M ≤
        Real.exp (-(Real.log 2 / 2) * (M : ℝ) ^ 3) := by
  have hc : 0 < Real.log 2 / 2 := div_pos (Real.log_pos (by norm_num)) (by norm_num)
  have ht : Tendsto (fun M : ℕ => (Real.log 2 / 2) * (M : ℝ) ^ 3) atTop atTop :=
    ((tendsto_pow_atTop (by norm_num : 3 ≠ 0)).comp (tendsto_natCast_atTop_atTop (R := ℝ))).const_mul_atTop hc
  apply Eventually.exists_forall_of_atTop
  filter_upwards [ht.eventually_ge_atTop (Real.log 91)] with M hM
  have he : 91 ≤ Real.exp ((Real.log 2 / 2) * (M : ℝ) ^ 3) := by
    simpa only [Real.exp_log (by norm_num : (0 : ℝ) < 91)] using Real.exp_le_exp.mpr hM
  apply (paperMiddle_preserved_deficit_bound M).trans
  calc
    _ ≤ Real.exp ((Real.log 2 / 2) * (M : ℝ) ^ 3) * Real.exp (-Real.log 2 * (M : ℝ) ^ 3) :=
      mul_le_mul_of_nonneg_right he (Real.exp_pos _).le
    _ = _ := by rw [← Real.exp_add]; congr 1; ring

/-- The paper's 200M^20 iterations supply its exp(-90M^20) accuracy including preservation. -/
theorem paperBottom_preserved_deficit_bound (M : ℕ) (hM : 1 ≤ M) :
    90 * paperScheduleMinG M + (1 / 2 : ℝ) ^ paperBottomIterations M ≤
      Real.exp (-90 * (M : ℝ) ^ 20) := by
  have hlog : (1 / 2 : ℝ) ≤ Real.log 2 := by
    have h := Real.one_sub_inv_le_log_of_pos (by norm_num : (0 : ℝ) < 2)
    norm_num at h
    exact h
  have hx : 1 ≤ (M : ℝ) ^ 20 := one_le_pow₀ (by exact_mod_cast hM)
  have hp : (1 / 2 : ℝ) ^ paperBottomIterations M ≤ Real.exp (-100 * (M : ℝ) ^ 20) := by
    rw [paper_half_pow_exp]
    simp only [paperBottomIterations, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_pow]
    apply Real.exp_le_exp.mpr
    nlinarith
  have htwo : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
  have hbig : (91 : ℝ) ≤ Real.exp 10 := by
    have h := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 2) htwo 10
    rw [← Real.exp_nat_mul] at h
    norm_num at h
    linarith
  have hmargin : (91 : ℝ) ≤ Real.exp (10 * (M : ℝ) ^ 20) :=
    hbig.trans (Real.exp_le_exp.mpr (by linarith))
  calc
    _ ≤ 91 * Real.exp (-100 * (M : ℝ) ^ 20) := by unfold paperScheduleMinG; linarith
    _ ≤ Real.exp (10 * (M : ℝ) ^ 20) * Real.exp (-100 * (M : ℝ) ^ 20) :=
      mul_le_mul_of_nonneg_right hmargin (Real.exp_pos _).le
    _ = _ := by rw [← Real.exp_add]; congr 1; ring

end BinaryFormMoat.GeometryIntegration

#print axioms BinaryFormMoat.GeometryIntegration.paperTailCheckpoint_labelledPoint_normalized_terminal

#print axioms BinaryFormMoat.GeometryIntegration.paperMiddle_preserved_deficit_bound
#print axioms BinaryFormMoat.GeometryIntegration.paperMiddle_preserved_deficit_eventually
#print axioms BinaryFormMoat.GeometryIntegration.paperBottom_preserved_deficit_bound

#print axioms BinaryFormMoat.GeometryIntegration.paperTailCheckpoint_labelledPoint_normalized_later
