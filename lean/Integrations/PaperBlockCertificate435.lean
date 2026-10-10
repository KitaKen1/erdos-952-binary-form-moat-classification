import Integrations.PaperCheckpointSchedule435
import Integrations.PaperTopTerminal435
import Integrations.PaperTailTerminal435

noncomputable section
open scoped Classical
namespace BinaryFormMoat.GeometryIntegration
open EntropyIntegration

/-- Actual scale at an ordinal of a block, including its recording ordinal. -/
def paperBlockScale (d M m : ℕ) (g0 : ℝ) (band : Fin 3) (V : ℝ) (j : ℕ) : ℝ :=
  paperBandScale (Real.exp (paperBandHi d m band)) (paperBandG M g0 band)
    (paperBandEntry (paperBandHi d m band) (paperBandG M g0 band) V + j)

/-- Operation witnesses use the original schedule's dependent finite type. -/
def paperBlockOp {d M : ℕ} (g0 : ℝ) (m : Fin (M + 1)) (band : Fin 3) (V : ℝ) (j : ℕ)
    (hfit : paperBandEntry (paperBandHi d m.val band) (paperBandG M g0 band) V + j <
      paperBandOperationCount d M m.val g0 band) : PaperScheduleOp d M g0 :=
  ⟨m, band, ⟨paperBandEntry (paperBandHi d m.val band) (paperBandG M g0 band) V + j, hfit⟩⟩

theorem paperBlockOp_mem {d M : ℕ} (g0 : ℝ) (m : Fin (M + 1))
    (hm : (M + 1) / 2 ≤ m.val) (band : Fin 3) (V : ℝ) (j : ℕ) (hfit) :
    paperBlockOp (d := d) g0 m band V j hfit ∈ paperScheduledOps d M g0 := by
  simpa only [paperScheduledOps, paperBlockOp, Finset.mem_filter, Finset.mem_univ, true_and] using hm

theorem paperBlockOp_g {d M : ℕ} (g0 : ℝ) (m : Fin (M + 1))
    (band : Fin 3) (V : ℝ) (j : ℕ) (hfit) :
    paperOpG (paperBlockOp (d := d) g0 m band V j hfit) = paperBandG M g0 band := rfl

theorem paperBlockOp_u {d M : ℕ} (g0 : ℝ) (m : Fin (M + 1))
    (band : Fin 3) (V : ℝ) (j : ℕ) (hfit) :
    paperOpU (paperBlockOp (d := d) g0 m band V j hfit) = paperBlockScale d M m.val g0 band V j := rfl

theorem paperBlockOp_position {d M : ℕ} (g0 : ℝ) (m : Fin (M + 1))
    (hm : (M + 1) / 2 ≤ m.val) (band : Fin 3) (V : ℝ) (j : ℕ)
    (hfit : paperBandEntry (paperBandHi d m.val band) (paperBandG M g0 band) V + j <
      paperBandOperationCount d M m.val g0 band) :
    paperOpPosition (paperBlockOp (d := d) g0 m band V j hfit) =
      paperOpPosition (paperBlockOp (d := d) g0 m band V 0 (by omega)) + j := by
  simpa only [paperBlockOp, Nat.add_zero] using paperOpPosition_block m hm band
    (paperBandEntry (paperBandHi d m.val band) (paperBandG M g0 band) V) j hfit

/-- A numerical certificate supplies every transition AND the recording
size/future budget. No entropy lower bound is an input to this certificate. -/
structure PaperBlockCertificate (f : Polynomial ℤ) (R M : ℕ) (m : Fin (M + 1))
    (g0 : ℝ) (band : Fin 3) (V : ℝ) (l : ℕ) (P : Finset ℕ) : Prop where
  fit : paperBandEntry (paperBandHi f.natDegree m.val band) (paperBandG M g0 band) V + l <
    paperBandOperationCount f.natDegree M m.val g0 band
  inputs : PaperInventoryBlockInputs f (R + 1) M m.val g0 band V l P
  record_size : paperEnrichmentSizeConstant f (R + 1) * primeBatchLogMean P ≤
    (paperBandG M g0 band) ^ 10 * paperBlockScale f.natDegree M m.val g0 band V l
  future_log : Real.log (paperFutureShift (paperBlockOp (d := f.natDegree) g0 m band V l fit) + 1 : ℕ) ≤
    2 * (paperOpG (paperBlockOp g0 m band V l fit) * paperOpU (paperBlockOp g0 m band V l fit))

/-- ONE threshold supplies full certificates for ANY fitted band block from
capacity and scale bounds, before source types, walks, laws and exact starts. -/
theorem paperSchedule_block_certificate_threshold (f : Polynomial ℤ) (R : ℕ)
    (hd : 1 ≤ f.natDegree) (g0 : ℝ) (hg0 : 0 < g0) (hg064 : g0 < 1 / 64) :
    ∃ M0 : ℕ, ∀ M ≥ M0, ∀ (m : Fin (M + 1)), (M + 1) / 2 ≤ m.val →
      ∀ (T : ℕ) (P : Finset ℕ), 2 ≤ T → 0 < P.card →
        (∀ p ∈ P, T ≤ p) → (∀ p ∈ P, p ≤ 2 * T) →
        Real.log T ≤ (21 / 20 : ℝ) * paperScheduleX f.natDegree m.val →
        ∀ (band : Fin 3) (V c : ℝ) (l : ℕ), 0 < V → Real.log V ≤ paperBandHi f.natDegree m.val band →
          paperBandEntry (paperBandHi f.natDegree m.val band) (paperBandG M g0 band) V + l <
            paperBandOperationCount f.natDegree M m.val g0 band →
          V ≤ (c / 2) * T → (c / 2) * ((T : ℝ) / Real.log T) ≤ (P.card : ℝ) →
          PaperBlockCertificate f R M m g0 band V l P := by
  obtain ⟨Mi, hi⟩ := paperSchedule_inventory_block_threshold f (R + 1) hd g0 hg0 hg064
  obtain ⟨Ms, hs⟩ := paperSchedule_uniform_size_threshold f (R + 1) hd g0 hg0
  obtain ⟨Mf, hf⟩ := paperSchedule_uniform_future_shift f.natDegree hd g0 hg0 (by linarith)
  refine ⟨max Mi (max Ms Mf), ?_⟩
  intro M hM m hm T P hT hPk hlo hhi hlog band V c l hV hVhi hfit hscale hcap
  have hMi : Mi ≤ M := (le_max_left _ _).trans hM
  have hMs : Ms ≤ M := (le_max_left _ _).trans ((le_max_right _ _).trans hM)
  have hMf : Mf ≤ M := (le_max_right _ _).trans ((le_max_right _ _).trans hM)
  have hin := hi M hMi m.val hm (by omega) band V c l T P hV hVhi hfit hscale hT hPk hlo hhi hcap hlog
  let o := paperBlockOp (d := f.natDegree) g0 m band V l hfit
  have ho := paperBlockOp_mem g0 m hm band V l hfit
  have hrec := hs M hMs (paperOpStage o ho hd hin.g_pos (by change paperBandG M g0 band < 1; linarith [hin.g_small]) T
    (primeBatchLogMean P) (by exact_mod_cast (by omega : 1 < T)) hlog
    (primeBatchLogMean_le_twolog P T hT hPk hlo hhi))
  exact ⟨hfit, hin, hrec, hf M hMf o ho⟩

end BinaryFormMoat.GeometryIntegration
#print axioms BinaryFormMoat.GeometryIntegration.paperBlockScale
#print axioms BinaryFormMoat.GeometryIntegration.paperBlockOp
#print axioms BinaryFormMoat.GeometryIntegration.paperBlockOp_mem
#print axioms BinaryFormMoat.GeometryIntegration.paperBlockOp_g
#print axioms BinaryFormMoat.GeometryIntegration.paperBlockOp_u
#print axioms BinaryFormMoat.GeometryIntegration.paperBlockOp_position
#print axioms BinaryFormMoat.GeometryIntegration.PaperBlockCertificate
#print axioms BinaryFormMoat.GeometryIntegration.paperSchedule_block_certificate_threshold
