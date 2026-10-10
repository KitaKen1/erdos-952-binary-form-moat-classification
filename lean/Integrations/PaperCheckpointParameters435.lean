import Integrations.PaperBandRoom435

noncomputable section
open scoped Topology Classical
namespace BinaryFormMoat.GeometryIntegration
open Filter

/-- The manuscript's fixed beta_0=1/(200d), halved at every checkpoint. -/
def paperCheckpointBeta (d i : ℕ) : ℝ := (1 / 2 : ℝ) ^ i / (200 * d)

/-- Closed form avoids a second recursive real-valued sequence. -/
def paperCheckpointRadius (d i : ℕ) : ℝ := 1 / (4 * d) - (1 - (1 / 2 : ℝ) ^ i) / (50 * d)

theorem paperCheckpointBeta_pos (d i : ℕ) (hd : 1 ≤ d) : 0 < paperCheckpointBeta d i := by
  have hdR : (0 : ℝ) < d := by exact_mod_cast (by omega : 0 < d)
  unfold paperCheckpointBeta
  positivity

theorem paperCheckpointBeta_succ (d i : ℕ) :
    paperCheckpointBeta d (i + 1) = paperCheckpointBeta d i / 2 := by
  unfold paperCheckpointBeta
  rw [pow_succ]
  ring

theorem paperCheckpointBeta_antitone (d : ℕ) (hd : 1 ≤ d) : Antitone (paperCheckpointBeta d) := by
  apply antitone_nat_of_succ_le
  intro i
  rw [paperCheckpointBeta_succ]
  linarith [paperCheckpointBeta_pos d i hd]

theorem paperCheckpointRadius_zero (d : ℕ) : paperCheckpointRadius d 0 = 1 / (4 * d) := by
  simp [paperCheckpointRadius]

theorem paperCheckpointRadius_eq (d i : ℕ) (hd : 1 ≤ d) :
    paperCheckpointRadius d i = 23 / (100 * d) + 4 * paperCheckpointBeta d i := by
  have hdR : (d : ℝ) ≠ 0 := by exact_mod_cast (by omega : d ≠ 0)
  unfold paperCheckpointRadius paperCheckpointBeta
  field_simp
  ring

theorem paperCheckpointRadius_succ (d i : ℕ) (hd : 1 ≤ d) :
    paperCheckpointRadius d (i + 1) = paperCheckpointRadius d i - 2 * paperCheckpointBeta d i := by
  rw [paperCheckpointRadius_eq d (i + 1) hd, paperCheckpointRadius_eq d i hd,
    paperCheckpointBeta_succ]
  ring

theorem paperCheckpointRadius_bounds (d i : ℕ) (hd : 1 ≤ d) :
    23 / (100 * d) < paperCheckpointRadius d i ∧ paperCheckpointRadius d i ≤ 1 / (4 * d) := by
  have hp := paperCheckpointBeta_pos d i hd
  have hl := paperCheckpointBeta_antitone d hd (Nat.zero_le i)
  have hzero := paperCheckpointRadius_eq d 0 hd
  rw [paperCheckpointRadius_zero] at hzero
  rw [paperCheckpointRadius_eq d i hd]
  constructor <;> linarith

theorem paperCheckpoint_exists_stop (d M : ℕ) (T : ℝ) (hM : 1 ≤ M) :
    ∃ i : ℕ, paperCheckpointBeta d i * Real.log T ≤ (M : ℝ) ^ 20 := by
  have hp : Tendsto (fun i : ℕ => paperCheckpointBeta d i * Real.log T) atTop (𝓝 0) := by
    simpa [paperCheckpointBeta] using
      (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2)
        (by norm_num : (1 / 2 : ℝ) < 1)).div_const (200 * d) |>.mul_const (Real.log T)
  have hm : (0 : ℝ) < (M : ℝ) ^ 20 := by
    have h : (0 : ℝ) < M := by exact_mod_cast (by omega : 0 < M)
    positivity
  obtain ⟨i, hi⟩ := (hp.eventually (gt_mem_nhds hm)).exists
  exact ⟨i, hi.le⟩

/-- Least stopping index; it is independent of the starting law and the walk. -/
def paperCheckpointStop (d M : ℕ) (T : ℝ) (hM : 1 ≤ M) : ℕ :=
  Nat.find (paperCheckpoint_exists_stop d M T hM)

theorem paperCheckpointStop_spec (d M : ℕ) (T : ℝ) (hM : 1 ≤ M) :
    paperCheckpointBeta d (paperCheckpointStop d M T hM) * Real.log T ≤ (M : ℝ) ^ 20 :=
  Nat.find_spec (paperCheckpoint_exists_stop d M T hM)

theorem paperCheckpointStop_before (d M : ℕ) (T : ℝ) (hM : 1 ≤ M) (i : ℕ)
    (hi : i < paperCheckpointStop d M T hM) :
    (M : ℝ) ^ 20 < paperCheckpointBeta d i * Real.log T :=
  lt_of_not_ge (Nat.find_min (paperCheckpoint_exists_stop d M T hM) hi)

theorem paperCheckpointStop_pos (d M : ℕ) (T : ℝ) (hM : 1 ≤ M)
    (hstart : (M : ℝ) ^ 20 < paperCheckpointBeta d 0 * Real.log T) :
    0 < paperCheckpointStop d M T hM := by
  by_contra hn
  have hz : paperCheckpointStop d M T hM = 0 := by omega
  have hs := paperCheckpointStop_spec d M T hM
  rw [hz] at hs
  linarith

theorem paperCheckpointStop_terminal_range (d M : ℕ) (T : ℝ) (hM : 1 ≤ M)
    (hstart : (M : ℝ) ^ 20 < paperCheckpointBeta d 0 * Real.log T) :
    (M : ℝ) ^ 20 / 2 < paperCheckpointBeta d (paperCheckpointStop d M T hM) * Real.log T ∧
      paperCheckpointBeta d (paperCheckpointStop d M T hM) * Real.log T ≤ (M : ℝ) ^ 20 := by
  have hp := paperCheckpointStop_pos d M T hM hstart
  obtain ⟨i, hi⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : paperCheckpointStop d M T hM ≠ 0)
  have hb := paperCheckpointStop_before d M T hM i (by omega)
  refine ⟨?_, paperCheckpointStop_spec d M T hM⟩
  rw [hi, paperCheckpointBeta_succ]
  nlinarith

end BinaryFormMoat.GeometryIntegration

#print axioms BinaryFormMoat.GeometryIntegration.paperCheckpointBeta
#print axioms BinaryFormMoat.GeometryIntegration.paperCheckpointRadius
#print axioms BinaryFormMoat.GeometryIntegration.paperCheckpointBeta_pos
#print axioms BinaryFormMoat.GeometryIntegration.paperCheckpointBeta_succ
#print axioms BinaryFormMoat.GeometryIntegration.paperCheckpointBeta_antitone
#print axioms BinaryFormMoat.GeometryIntegration.paperCheckpointRadius_zero
#print axioms BinaryFormMoat.GeometryIntegration.paperCheckpointRadius_eq
#print axioms BinaryFormMoat.GeometryIntegration.paperCheckpointRadius_succ
#print axioms BinaryFormMoat.GeometryIntegration.paperCheckpointRadius_bounds
#print axioms BinaryFormMoat.GeometryIntegration.paperCheckpoint_exists_stop
#print axioms BinaryFormMoat.GeometryIntegration.paperCheckpointStop
#print axioms BinaryFormMoat.GeometryIntegration.paperCheckpointStop_spec
#print axioms BinaryFormMoat.GeometryIntegration.paperCheckpointStop_before
#print axioms BinaryFormMoat.GeometryIntegration.paperCheckpointStop_pos
#print axioms BinaryFormMoat.GeometryIntegration.paperCheckpointStop_terminal_range
