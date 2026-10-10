import Integrations.PassingQuota435

noncomputable section
namespace BinaryFormMoat.EntropyIntegration
open MeasureTheory ProbabilityTheory

/-- A fixed constant for ALL primes of a dyadic batch. -/
def paperPassingConstant (τ β : ℝ) : ℝ := 2 + 32 * β / τ

/-- ONE integer quota, chosen before prime/root/candidate/residue data. -/
def paperPassingCount (T L : ℕ) (τ β : ℝ) : ℕ :=
  max 1 ⌈paperPassingConstant τ β * ((T : ℝ) / L) * Real.log T⌉₊

theorem paperPassingCount_pos (T L : ℕ) (τ β : ℝ) : 0 < paperPassingCount T L τ β :=
  lt_of_lt_of_le Nat.zero_lt_one (Nat.le_max_left _ _)

theorem paperPassingConstant_bounds (τ β : ℝ) (hτ : 0 < τ) (hβ : 0 ≤ β) :
    2 ≤ paperPassingConstant τ β ∧ 32 * β ≤ paperPassingConstant τ β * τ := by
  unfold paperPassingConstant
  constructor
  · exact le_add_of_nonneg_right (div_nonneg (mul_nonneg (by norm_num) hβ) hτ.le)
  · have he : (2 + 32 * β / τ) * τ = 2 * τ + 32 * β := by field_simp
    rw [he]
    linarith

theorem paperPassingCount_upper (T L : ℕ) (hT : 2 ≤ T) (hL : 1 ≤ L) (hLT : L ≤ T)
    (τ β : ℝ) (hτ : 0 < τ) (hβ : 0 ≤ β) :
    (paperPassingCount T L τ β : ℝ) ≤
      2 * paperPassingConstant τ β * ((T : ℝ) / L) * Real.log T := by
  have hLp : (0 : ℝ) < L := by exact_mod_cast (by omega : 0 < L)
  have hratio : (1 : ℝ) ≤ (T : ℝ) / L := (one_le_div hLp).mpr (by exact_mod_cast hLT)
  have hlog : (1 : ℝ) / 2 ≤ Real.log T := by
    have h2 := Real.one_sub_inv_le_log_of_pos (by norm_num : (0 : ℝ) < 2)
    have ht := Real.log_le_log (by norm_num : (0 : ℝ) < 2) (by exact_mod_cast hT : (2 : ℝ) ≤ T)
    norm_num at h2
    exact h2.trans ht
  have hK := (paperPassingConstant_bounds τ β hτ hβ).1
  have hx : 1 ≤ paperPassingConstant τ β * ((T : ℝ) / L) * Real.log T := by
    have hprod := mul_le_mul hK hratio (by norm_num : (0 : ℝ) ≤ 1) (by linarith : 0 ≤ paperPassingConstant τ β)
    have h := mul_le_mul hprod hlog (by norm_num : (0 : ℝ) ≤ 1 / 2) (by positivity : 0 ≤ paperPassingConstant τ β * ((T : ℝ) / L))
    norm_num at h
    exact h
  have hc := Nat.ceil_lt_add_one (by linarith : 0 ≤ paperPassingConstant τ β * ((T : ℝ) / L) * Real.log T)
  unfold paperPassingCount
  rw [Nat.cast_max, Nat.cast_one]
  apply max_le <;> nlinarith

/-- The common quota pays beta*log(p) uniformly for T<=p<=2T. -/
theorem paperPassingCount_exponent (T L p : ℕ) (hT : 2 ≤ T) (hL : 1 ≤ L)
    (hlo : T ≤ p) (hhi : p ≤ 2 * T) (τ β : ℝ) (hτ : 0 < τ) (hβ : 0 ≤ β) :
    β * Real.log p ≤ (paperPassingCount T L τ β : ℝ) * ((L : ℝ) * (τ / p) / 8) := by
  have hTp : (0 : ℝ) < T := by exact_mod_cast (by omega : 0 < T)
  have hLp : (0 : ℝ) < L := by exact_mod_cast (by omega : 0 < L)
  have hpp : (0 : ℝ) < p := by exact_mod_cast (by omega : 0 < p)
  have hlogT : 0 ≤ Real.log T := Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ T))
  have hlogp : Real.log p ≤ 2 * Real.log T := by
    have hp := Real.log_le_log hpp (by exact_mod_cast hhi : (p : ℝ) ≤ 2 * T)
    rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) hTp.ne'] at hp
    have h2 := Real.log_le_log (by norm_num : (0 : ℝ) < 2) (by exact_mod_cast hT : (2 : ℝ) ≤ T)
    linarith
  have hK := paperPassingConstant_bounds τ β hτ hβ
  have hKp : 0 ≤ paperPassingConstant τ β := by linarith [hK.1]
  have hceil : paperPassingConstant τ β * ((T : ℝ) / L) * Real.log T ≤
      (paperPassingCount T L τ β : ℝ) :=
    (Nat.le_ceil _).trans (Nat.cast_le.mpr (Nat.le_max_right 1 _))
  have hden : paperPassingConstant τ β * τ / 16 ≤ paperPassingConstant τ β * τ * T / (8 * p) := by
    have hpd : (8 : ℝ) * p ≤ 16 * T := by exact_mod_cast (show 8 * p ≤ 16 * T by omega)
    have h := div_le_div_of_nonneg_left (by positivity : 0 ≤ paperPassingConstant τ β * τ * T)
      (by positivity : (0 : ℝ) < 8 * p) hpd
    convert h using 1
    field_simp
  calc
    _ ≤ 2 * β * Real.log T := by nlinarith [mul_le_mul_of_nonneg_left hlogp hβ]
    _ ≤ (paperPassingConstant τ β * τ / 16) * Real.log T := by
      apply mul_le_mul_of_nonneg_right _ hlogT
      linarith [hK.2]
    _ ≤ (paperPassingConstant τ β * τ * T / (8 * p)) * Real.log T :=
      mul_le_mul_of_nonneg_right hden hlogT
    _ = (paperPassingConstant τ β * ((T : ℝ) / L) * Real.log T) * ((L : ℝ) * (τ / p) / 8) := by
      field_simp
    _ ≤ _ := mul_le_mul_of_nonneg_right hceil (by positivity)

theorem paperPassingCount_survivor_tail (T L p : ℕ) (hT : 2 ≤ T) (hL : 1 ≤ L)
    (hlo : T ≤ p) (hhi : p ≤ 2 * T) (τ β : ℝ) (hτ : 0 < τ) (hβ : 0 ≤ β) :
    (p : ℝ) * Real.exp (-(paperPassingCount T L τ β : ℝ) * ((L : ℝ) * (τ / p) / 8)) ≤
      (p : ℝ) ^ (1 - β) := by
  have hpp : (0 : ℝ) < p := by exact_mod_cast (by omega : 0 < p)
  have he : Real.exp (-(paperPassingCount T L τ β : ℝ) * ((L : ℝ) * (τ / p) / 8)) ≤
      Real.exp (-β * Real.log p) := by
    apply Real.exp_le_exp.mpr
    linarith [paperPassingCount_exponent T L p hT hL hlo hhi τ β hτ hβ]
  apply (mul_le_mul_of_nonneg_left he hpp.le).trans_eq
  rw [Real.rpow_def_of_pos hpp, ← Real.exp_log hpp, ← Real.exp_add]
  simp only [Real.log_exp]
  congr 1
  ring

/-- The paper's 5*p^(1-beta) list bound uses the SAME quota for every
coordinate and every positive posterior data value. -/
theorem expected_passingList_common_quota {H : Type*} [Fintype H]
    [MeasurableSpace H] [MeasurableSingletonClass H]
    (ν : Measure H) [IsProbabilityMeasure ν] (T L p : ℕ) [NeZero p]
    (hT : 2 ≤ T) (hL : 1 ≤ L) (hlo : T ≤ p) (hhi : p ≤ 2 * T)
    (τ β : ℝ) (hτ : 0 < τ) (hβ : 0 ≤ β) (reject : ZMod p → H → Prop)
    (B : Finset (ZMod p))
    (hB : (B.card : ℝ) ≤ 4 * (p : ℝ) ^ (1 - β))
    (hfloor : ∀ x ∉ B, (L : ℝ) * (τ / p) / 8 ≤ ν.real {h | reject x h}) :
    (∫ h : Fin (paperPassingCount T L τ β) → H, ((passingList reject h).card : ℝ)
      ∂Measure.pi (fun _ : Fin (paperPassingCount T L τ β) => ν)) ≤ 5 * (p : ℝ) ^ (1 - β) := by
  apply expected_passingList_card_source_bound ν reject B ((L : ℝ) * (τ / p) / 8)
    ((p : ℝ) ^ (1 - β)) hfloor hB
  simpa only [Fintype.card_fin, ZMod.card] using
    paperPassingCount_survivor_tail T L p hT hL hlo hhi τ β hτ hβ

end BinaryFormMoat.EntropyIntegration
#print axioms BinaryFormMoat.EntropyIntegration.paperPassingConstant
#print axioms BinaryFormMoat.EntropyIntegration.paperPassingCount
#print axioms BinaryFormMoat.EntropyIntegration.paperPassingCount_pos
#print axioms BinaryFormMoat.EntropyIntegration.paperPassingConstant_bounds
#print axioms BinaryFormMoat.EntropyIntegration.paperPassingCount_upper
#print axioms BinaryFormMoat.EntropyIntegration.paperPassingCount_exponent
#print axioms BinaryFormMoat.EntropyIntegration.paperPassingCount_survivor_tail
#print axioms BinaryFormMoat.EntropyIntegration.expected_passingList_common_quota
