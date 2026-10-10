import Integrations.PaperBlockCertificate435

noncomputable section
open scoped Classical
namespace BinaryFormMoat.GeometryIntegration
open EntropyIntegration

def paperBottomTarget (d m : ℕ) : ℝ := Real.exp (paperBandHi d m 2)

theorem paperBottomTarget_entry (d M m : ℕ) (g0 : ℝ) :
    paperBandEntry (paperBandHi d m 2) (paperBandG M g0 2) (paperBottomTarget d m) = 0 := by
  simp [paperBandEntry, paperBottomTarget]

/-- The first bottom scale is smaller than the largest middle target. -/
theorem paperBottomTarget_le_checkpoint_zero (d m : ℕ) (hd : 1 ≤ d) (T : ℝ)
    (hlo : paperScheduleX d m ≤ Real.log T) :
    paperBottomTarget d m ≤ paperCheckpointTarget d T 0 := by
  have hdR : (0 : ℝ) < d := by exact_mod_cast (by omega : 0 < d)
  have hx := paperScheduleX_pos d m hd
  apply Real.exp_le_exp.mpr
  rw [paperCheckpointRadius_zero]
  norm_num [paperBandHi, div_eq_mul_inv] at ⊢
  nlinarith [mul_nonneg (sub_nonneg.mpr hlo) (inv_pos.mpr hdR).le,
    mul_pos hx (inv_pos.mpr hdR)]

/-- All bottom transitions AND the recording operation fit at one threshold. -/
theorem paperBottom_uniform_blocks (d : ℕ) (hd : 1 ≤ d) :
    ∃ M0 : ℕ, ∀ M ≥ M0, ∀ m : ℕ, (M + 1) / 2 ≤ m → ∀ g0 : ℝ,
      paperBandEntry (paperBandHi d m 2) (paperBandG M g0 2) (paperBottomTarget d m) +
        paperBottomIterations M < paperBandOperationCount d M m g0 2 := by
  obtain ⟨M0, hroom⟩ := paperSchedule_bottom_iterations_fit d hd
  refine ⟨max M0 1, ?_⟩
  intro M hM m hm g0
  have hM1 : 1 ≤ M := (le_max_right _ _).trans hM
  have hg : 0 < paperScheduleMinG M := Real.exp_pos _
  have hg1 : paperScheduleMinG M < 1 := by
    apply Real.exp_lt_one_iff.mpr
    have hMR : (0 : ℝ) < M := by exact_mod_cast (by omega : 0 < M)
    have hp : (0 : ℝ) < (M : ℝ) ^ 20 := by positivity
    nlinarith
  have hgb : paperBandG M g0 2 = paperScheduleMinG M := by simp [paperBandG]
  have hs := hroom M ((le_max_left _ _).trans hM) m hm
  have hf := paperBandEntry_block_fits (paperBandLo d m 2) (paperBandHi d m 2)
    (paperScheduleMinG M) (paperBottomTarget d m) hg hg1
    (by simp [paperBottomTarget]) (paperBottomIterations M)
    (by rw [paperBottomTarget, Real.log_exp]; linarith)
  simpa only [paperBandOperationCount, hgb] using hf

/-- ONE batch, chosen before walks and laws, supplies every middle checkpoint
and the bottom block, including record-size and future-budget certificates. -/
theorem paperSchedule_middle_bottom_batches (f : Polynomial ℤ) (hf : Irreducible f)
    (hd : 2 ≤ f.natDegree) (R : ℕ) (g0 : ℝ) (hg0 : 0 < g0) (hg064 : g0 < 1 / 64) :
    ∃ c : ℝ, 0 < c ∧ ∀ bad : Finset ℕ, ∃ M0 : ℕ, ∀ M ≥ M0,
      ∀ (m : Fin (M + 1)), (M + 1) / 2 ≤ m.val → ∀ T : ℕ, 2 ≤ T →
        paperScheduleX f.natDegree m.val ≤ Real.log T →
        Real.log T ≤ (21 / 20 : ℝ) * paperScheduleX f.natDegree m.val →
        ∃ P : Finset ℕ, P.card = paperPrimeCount c T ∧ Disjoint P bad ∧
          (∀ p ∈ P, p.Prime ∧ T ≤ p ∧ p ≤ 2 * T ∧ (primeRootSet f p).card = f.natDegree) ∧
          0 < P.card ∧ (P.card : ℝ) * Real.log (2 * T : ℕ) ≤ 2 * c * T ∧
          (∀ i : ℕ, PaperBlockCertificate f R M m g0 1 (paperCheckpointTarget f.natDegree T i)
            (paperMiddleIterations M) P) ∧
          PaperBlockCertificate f R M m g0 2 (paperBottomTarget f.natDegree m.val)
            (paperBottomIterations M) P := by
  obtain ⟨c, hc, hsupply⟩ := exists_paper_prime_inventory f hf hd
  refine ⟨c, hc, ?_⟩
  intro bad
  obtain ⟨T0, hT0⟩ := (hsupply bad).exists_forall_of_atTop
  obtain ⟨Mt, ht⟩ := paperSchedule_uniform_batch_threshold f.natDegree (by omega) T0
  obtain ⟨Mi, hi⟩ := paperSchedule_block_certificate_threshold f R (by omega) g0 hg0 hg064
  obtain ⟨Mm, hmfit⟩ := paperCheckpoint_uniform_middle_blocks f.natDegree (by omega)
  obtain ⟨Mb, hbfit⟩ := paperBottom_uniform_blocks f.natDegree (by omega)
  obtain ⟨Mc, hscale⟩ := paperCheckpoint_uniform_inventory_scale f.natDegree (by omega) c hc
  refine ⟨Mt + Mi + Mm + Mb + Mc, ?_⟩
  intro M hM m hm T hT hlo hhi
  have hMt : Mt ≤ M := by omega
  have hMi : Mi ≤ M := by omega
  have hMm : Mm ≤ M := by omega
  have hMb : Mb ≤ M := by omega
  have hMc : Mc ≤ M := by omega
  obtain ⟨P, hPc, hbad, hP, hPk, hcap, _, hAlpha, _⟩ := hT0 T (ht M hMt m.val hm T hlo)
  have hPl : ∀ p ∈ P, T ≤ p := fun p hp => (hP p hp).2.1
  have hPh : ∀ p ∈ P, p ≤ 2 * T := fun p hp => (hP p hp).2.2.1
  have hmid : paperBandG M g0 1 = paperScheduleMiddleG M := by simp [paperBandG]
  have hvhi (i : ℕ) : Real.log (paperCheckpointTarget f.natDegree T i) ≤ paperBandHi f.natDegree m.val 1 := by
    have hs := (paperCheckpointTarget_log_bounds f.natDegree m.val (by omega) T hlo hhi i).2
    have hdR : (0 : ℝ) < f.natDegree := by exact_mod_cast (by omega : 0 < f.natDegree)
    norm_num [paperBandHi, div_eq_mul_inv] at hs ⊢
    nlinarith [mul_pos (paperScheduleX_pos f.natDegree m.val (by omega)) (inv_pos.mpr hdR)]
  have htarget (i : ℕ) : paperCheckpointTarget f.natDegree T i ≤ (c / 2) * T := by
    exact hscale M hMc m.val hm T (by exact_mod_cast (by omega : 0 < T)) hlo i
  refine ⟨P, hPc, hbad, hP, hPk, hAlpha, ?_, ?_⟩
  · intro i
    apply hi M hMi m hm T P hT hPk hPl hPh hhi 1 _ c (paperMiddleIterations M)
      (paperCheckpointTarget_pos _ _ _) (hvhi i)
    · simpa only [hmid] using hmfit M hMm m.val hm T g0 hlo hhi i
    · exact htarget i
    · exact hcap
  · apply hi M hMi m hm T P hT hPk hPl hPh hhi 2 _ c (paperBottomIterations M)
      (Real.exp_pos _) (by simp) (hbfit M hMb m.val hm g0)
    · exact (paperBottomTarget_le_checkpoint_zero f.natDegree m.val (by omega) T hlo).trans (htarget 0)
    · exact hcap

/-- Every final middle checkpoint precedes the first bottom operation in the
original list. This supplies the conditional bottom-start ordering premise. -/
theorem paperMiddleCheckpoint_before_bottom {d M : ℕ} (g0 : ℝ) (m : Fin (M + 1))
    (hm : (M + 1) / 2 ≤ m.val) (T : ℝ) (i : ℕ)
    (hmid : paperBandEntry (paperBandHi d m.val 1) (paperScheduleMiddleG M) (paperCheckpointTarget d T i) <
      paperBandOperationCount d M m.val g0 1)
    (hbot : paperBandEntry (paperBandHi d m.val 2) (paperBandG M g0 2) (paperBottomTarget d m.val) <
      paperBandOperationCount d M m.val g0 2) :
    paperOpPosition (paperMiddleCheckpointOp (d := d) g0 m T i hmid) ≤
      paperOpPosition (paperBlockOp (d := d) g0 m 2 (paperBottomTarget d m.val) 0 (by simpa using hbot)) := by
  apply (paperOpPosition_le_iff _ _ (paperMiddleCheckpointOp_mem g0 m hm T i hmid)
    (paperBlockOp_mem g0 m hm 2 (paperBottomTarget d m.val) 0 (by simpa using hbot))).mpr
  unfold paperOpLater
  right; left
  exact ⟨rfl, by change (1 : Fin 3) < 2; decide⟩

end BinaryFormMoat.GeometryIntegration
#print axioms BinaryFormMoat.GeometryIntegration.paperBottomTarget
#print axioms BinaryFormMoat.GeometryIntegration.paperBottomTarget_entry
#print axioms BinaryFormMoat.GeometryIntegration.paperBottomTarget_le_checkpoint_zero
#print axioms BinaryFormMoat.GeometryIntegration.paperBottom_uniform_blocks
#print axioms BinaryFormMoat.GeometryIntegration.paperSchedule_middle_bottom_batches
#print axioms BinaryFormMoat.GeometryIntegration.paperMiddleCheckpoint_before_bottom
