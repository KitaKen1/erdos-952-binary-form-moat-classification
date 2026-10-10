import Integrations.ShortWordResidues435
import Mathlib.Data.Nat.Log

noncomputable section
namespace BinaryFormMoat.EntropyIntegration

/-- Exact integer construction of the manuscript's degree-dependent dyadic
word length. Avoids real logarithm floors in the separation proof. -/
def rootWordLevel (d T : ℕ) : ℕ := Nat.log 2 T / (2 * d)
def rootWordLength (d T : ℕ) : ℕ := 2 ^ rootWordLevel d T

theorem rootWordLength_pos (d T : ℕ) : 0 < rootWordLength d T := by
  unfold rootWordLength
  positivity

theorem rootWordLevel_mono (d : ℕ) : Monotone (rootWordLevel d) := by
  intro T U h
  exact Nat.div_le_div_right (Nat.log_mono_right h)

theorem rootWordLength_mono (d : ℕ) : Monotone (rootWordLength d) := by
  intro T U h
  exact Nat.pow_le_pow_right (by norm_num) (rootWordLevel_mono d h)

theorem rootWordLength_power_le (d T : ℕ) (hT : 1 ≤ T) :
    rootWordLength d T ^ (2 * d) ≤ T := by
  rw [rootWordLength, ← pow_mul]
  exact (Nat.pow_le_pow_right (by norm_num)
    (Nat.div_mul_le_self (Nat.log 2 T) (2 * d))).trans (Nat.pow_log_le_self 2 (by omega))

theorem rootWordLength_next_power_gt (d T : ℕ) (hd : 1 ≤ d) :
    T < (2 * rootWordLength d T) ^ (2 * d) := by
  have he : Nat.log 2 T + 1 ≤ (rootWordLevel d T + 1) * (2 * d) := by
    have h := (Nat.div_lt_iff_lt_mul (by omega : 0 < 2 * d)).mp
      (Nat.lt_succ_self (Nat.log 2 T / (2 * d)))
    change Nat.log 2 T + 1 ≤ (Nat.log 2 T / (2 * d) + 1) * (2 * d)
    exact Nat.succ_le_of_lt (by simpa only [Nat.succ_eq_add_one] using h)
  apply (Nat.lt_pow_succ_log_self (by norm_num : 1 < 2) T).trans_le
  have hp := Nat.pow_le_pow_right (by norm_num : 1 ≤ 2) he
  rw [rootWordLength, mul_comm 2 _, ← pow_succ, ← pow_mul]
  exact hp

theorem rootWordLength_le (d T : ℕ) (hd : 1 ≤ d) (hT : 1 ≤ T) :
    rootWordLength d T ≤ T := by
  have h := rootWordLength_power_le d T hT
  exact (Nat.le_self_pow (by omega : 2 * d ≠ 0) _).trans h

theorem rootWordLength_dvd (d T U : ℕ) (h : T ≤ U) :
    rootWordLength d T ∣ rootWordLength d U := by
  exact pow_dvd_pow 2 (rootWordLevel_mono d h)

/-- A deliberately coarse fixed threshold suffices; the classification
requires existence rather than an optimized numerical moat radius. -/
def rootWordSeparationThreshold (f : Polynomial ℤ) (R : ℕ) : ℕ :=
  2 ^ (2 * f.natDegree * (coefficientBound f f.natDegree * (R + 1) ^ f.natDegree + 1))

theorem rootWordLength_separation (f : Polynomial ℤ) (R T : ℕ)
    (hd : 1 ≤ f.natDegree) (hT : rootWordSeparationThreshold f R ≤ T) :
    coefficientBound f f.natDegree * ((R + 1) * rootWordLength f.natDegree T) ^ f.natDegree < T := by
  let C := coefficientBound f f.natDegree * (R + 1) ^ f.natDegree
  have ht : 1 ≤ T := by
    have hp : 0 < rootWordSeparationThreshold f R := by unfold rootWordSeparationThreshold; positivity
    omega
  have hl : C + 1 ≤ rootWordLevel f.natDegree T := by
    have he := Nat.le_log_of_pow_le (by norm_num : 1 < 2) hT
    change 2 * f.natDegree * (C + 1) ≤ Nat.log 2 T at he
    unfold rootWordLevel
    exact (Nat.le_div_iff_mul_le (by omega : 0 < 2 * f.natDegree)).mpr (by simpa [mul_comm] using he)
  have hc : C < rootWordLength f.natDegree T := by
    have hpow := Nat.pow_le_pow_right (by norm_num : 1 ≤ 2) hl
    -- The elementary exponential bound is stronger than the needed linear one.
    have hlin : C + 1 ≤ 2 ^ (C + 1) := by
      induction C with
      | zero => norm_num
      | succ C ih => rw [pow_succ]; omega
    exact (Nat.lt_succ_self C).trans_le (hlin.trans hpow)
  have hp : C < rootWordLength f.natDegree T ^ f.natDegree :=
    hc.trans_le (Nat.le_self_pow (by omega : f.natDegree ≠ 0) _)
  have hs := Nat.mul_lt_mul_of_pos_right hp
    (pow_pos (rootWordLength_pos f.natDegree T) f.natDegree)
  have hb := rootWordLength_power_le f.natDegree T ht
  have he : 2 * f.natDegree = f.natDegree + f.natDegree := by omega
  rw [he, pow_add] at hb
  simpa only [C, mul_pow, mul_assoc] using hs.trans_le hb

end BinaryFormMoat.EntropyIntegration
#print axioms BinaryFormMoat.EntropyIntegration.rootWordLevel
#print axioms BinaryFormMoat.EntropyIntegration.rootWordLength
#print axioms BinaryFormMoat.EntropyIntegration.rootWordLength_pos
#print axioms BinaryFormMoat.EntropyIntegration.rootWordLevel_mono
#print axioms BinaryFormMoat.EntropyIntegration.rootWordLength_mono
#print axioms BinaryFormMoat.EntropyIntegration.rootWordLength_power_le
#print axioms BinaryFormMoat.EntropyIntegration.rootWordLength_next_power_gt
#print axioms BinaryFormMoat.EntropyIntegration.rootWordLength_le
#print axioms BinaryFormMoat.EntropyIntegration.rootWordLength_dvd
#print axioms BinaryFormMoat.EntropyIntegration.rootWordSeparationThreshold
#print axioms BinaryFormMoat.EntropyIntegration.rootWordLength_separation
