import Integrations.TauHarper435
import Integrations.PaperScheduleBands435

noncomputable section
open scoped Classical Topology
namespace BinaryFormMoat.GeometryIntegration
open Filter EntropyIntegration TauHarperIntegration

/-- Fixed-size good-prime batches give both the required supply and a small
upper alphabet budget; their size is selected before any walk or scale block. -/
def paperPrimeCount (c : ℝ) (T : ℕ) : ℕ := ⌊c * ((T : ℝ) / Real.log T)⌋₊

theorem paperPrimeCount_bounds (c : ℝ) (T : ℕ)
    (hlarge : 2 ≤ c * ((T : ℝ) / Real.log T)) :
    0 < paperPrimeCount c T ∧
      (c / 2) * ((T : ℝ) / Real.log T) ≤ (paperPrimeCount c T : ℝ) ∧
      (paperPrimeCount c T : ℝ) ≤ c * ((T : ℝ) / Real.log T) := by
  have hlo := Nat.lt_floor_add_one (c * ((T : ℝ) / Real.log T))
  have hhi := Nat.floor_le (by linarith : 0 ≤ c * ((T : ℝ) / Real.log T))
  have hp : 0 < paperPrimeCount c T := Nat.floor_pos.mpr (by linarith)
  refine ⟨hp, ?_, hhi⟩
  change (c / 2) * ((T : ℝ) / Real.log T) ≤ (⌊c * ((T : ℝ) / Real.log T)⌋₊ : ℝ)
  linarith

/-- Supply times the TRUE mean prime logarithm covers every smaller input
rank, without replacing the mean by the lower endpoint in entropy formulas. -/
theorem paperPrimeInventory_of_capacity (P : Finset ℕ) (T : ℕ) (c : ℝ)
    (hT : 2 ≤ T) (hPk : 0 < P.card) (hlo : ∀ p ∈ P, T ≤ p)
    (hhi : ∀ p ∈ P, p ≤ 2 * T)
    (hcapacity : (c / 2) * ((T : ℝ) / Real.log T) ≤ (P.card : ℝ))
    (U : ℝ) (hU : 0 ≤ U) (hscale : U ≤ (c / 2) * T) :
    paperInputRank U (primeBatchLogMean P) ≤ P.card := by
  have hlog : 0 < Real.log (T : ℝ) := Real.log_pos (by exact_mod_cast hT)
  have hL := primeBatchLogMean_dyadic_bounds P T hT hPk hlo hhi
  have hc : (c / 2) * T ≤ (P.card : ℝ) * Real.log T := by
    apply (div_le_iff₀ hlog).mp
    simpa only [mul_div_assoc] using hcapacity
  have hmass : U ≤ (P.card : ℝ) * primeBatchLogMean P :=
    hscale.trans (hc.trans (mul_le_mul_of_nonneg_left hL.2.1 (Nat.cast_nonneg _)))
  have hf := (Nat.floor_le (div_nonneg hU hL.1.le)).trans ((div_le_iff₀ hL.1).mpr hmass)
  exact_mod_cast hf

theorem paperPrimeInventory_geometric_scales (P : Finset ℕ) (T : ℕ) (c U g : ℝ)
    (hT : 2 ≤ T) (hPk : 0 < P.card) (hlo : ∀ p ∈ P, T ≤ p)
    (hhi : ∀ p ∈ P, p ≤ 2 * T)
    (hcapacity : (c / 2) * ((T : ℝ) / Real.log T) ≤ (P.card : ℝ))
    (hU : 0 ≤ U) (hscale : U ≤ (c / 2) * T) (hg : 0 ≤ g) (hg1 : g ≤ 1) (n : ℕ) :
    paperInputRank (paperBandScale U g n) (primeBatchLogMean P) ≤ P.card := by
  apply paperPrimeInventory_of_capacity P T c hT hPk hlo hhi hcapacity _
    (by unfold paperBandScale; positivity)
  have hu : paperBandScale U g n ≤ U := by
    simpa [paperBandScale] using paperBandScale_antitone U g hU hg hg1 (Nat.zero_le n)
  exact hu.trans hscale

/-- A constructed batch has linear-in-T full alphabet cost as well as supply. -/
theorem paperPrimeAlphabet_budget (P : Finset ℕ) (T : ℕ) (c : ℝ)
    (hT : 2 ≤ T) (hPk : 0 < P.card) (hlo : ∀ p ∈ P, T ≤ p)
    (hhi : ∀ p ∈ P, p ≤ 2 * T)
    (hcapacity : (P.card : ℝ) ≤ c * ((T : ℝ) / Real.log T)) :
    (P.card : ℝ) * Real.log (2 * T : ℕ) ≤ 2 * c * T ∧
      (P.card : ℝ) * primeBatchLogMean P ≤ 2 * c * T := by
  have hlog : 0 < Real.log (T : ℝ) := Real.log_pos (by exact_mod_cast hT)
  have hL := primeBatchLogMean_dyadic_bounds P T hT hPk hlo hhi
  have hc : (P.card : ℝ) * Real.log T ≤ c * T := by
    apply (le_div_iff₀ hlog).mp
    simpa only [mul_div_assoc] using hcapacity
  have hl2 : Real.log 2 ≤ Real.log (T : ℝ) := Real.log_le_log (by norm_num) (by exact_mod_cast hT)
  have htw : Real.log (2 * T : ℕ) ≤ 2 * Real.log (T : ℝ) := by
    rw [Nat.cast_mul, Nat.cast_ofNat, Real.log_mul (by norm_num) (by positivity)]
    linarith
  have hh := mul_le_mul_of_nonneg_left htw (Nat.cast_nonneg P.card)
  have hbound : (P.card : ℝ) * Real.log (2 * T : ℕ) ≤ 2 * c * T := by nlinarith
  exact ⟨hbound, (mul_le_mul_of_nonneg_left hL.2.2.1 (Nat.cast_nonneg _)).trans hbound⟩

/-- ONE supply constant before every finite exclusion. The resulting batch is
chosen before all walks, starting laws, geometric scales and root labels. -/
theorem exists_paper_prime_inventory (f : Polynomial ℤ) (hf : Irreducible f)
    (hd : 2 ≤ f.natDegree) :
    ∃ c : ℝ, 0 < c ∧ ∀ bad : Finset ℕ, ∀ᶠ T : ℕ in atTop,
      ∃ P : Finset ℕ, P.card = paperPrimeCount c T ∧ Disjoint P bad ∧
        (∀ p ∈ P, p.Prime ∧ T ≤ p ∧ p ≤ 2 * T ∧ (primeRootSet f p).card = f.natDegree) ∧
        0 < P.card ∧
        (c / 2) * ((T : ℝ) / Real.log T) ≤ (P.card : ℝ) ∧
        (P.card : ℝ) ≤ c * ((T : ℝ) / Real.log T) ∧
        (P.card : ℝ) * Real.log (2 * T : ℕ) ≤ 2 * c * T ∧
        (∀ U : ℝ, 0 ≤ U → U ≤ (c / 2) * T → paperInputRank U (primeBatchLogMean P) ≤ P.card) := by
  obtain ⟨c, hc, hquota⟩ := exists_irreducible_nat_root_quota f hf hd
  refine ⟨c, hc, fun bad => ?_⟩
  have hlarge : ∀ᶠ T : ℕ in atTop, 2 ≤ c * ((T : ℝ) / Real.log T) :=
    ((tendsto_primeCountingScale.comp (tendsto_natCast_atTop_atTop (R := ℝ))).const_mul_atTop hc).eventually_ge_atTop 2
  filter_upwards [hquota bad, hlarge, eventually_ge_atTop (2 : ℕ)] with T hq hl hT
  obtain ⟨hp, hlow, hhigh⟩ := paperPrimeCount_bounds c T hl
  obtain ⟨P, hcard, hbad, hP⟩ := hq (paperPrimeCount c T) hhigh
  have hPk : 0 < P.card := by simpa [hcard] using hp
  have hlo := fun p h => (hP p h).2.1
  have hhi := fun p h => (hP p h).2.2.1
  rw [← hcard] at hlow hhigh
  refine ⟨P, hcard, hbad, ?_, hPk, hlow, hhigh,
    (paperPrimeAlphabet_budget P T c hT hPk hlo hhi hhigh).1, ?_⟩
  · intro p hp
    exact ⟨(hP p hp).1, hlo p hp, hhi p hp,
      by rw [card_primeRootSet f p (hP p hp).1, (hP p hp).2.2.2]⟩
  · intro U hU hscale
    exact paperPrimeInventory_of_capacity P T c hT hPk hlo hhi hlow U hU hscale

/-- Any fixed arithmetic threshold is reached simultaneously by every integer
batch scale in every selected window, even though the window family grows. -/
theorem paperSchedule_uniform_batch_threshold (d : ℕ) (hd : 1 ≤ d) (T0 : ℕ) :
    ∃ M0 : ℕ, ∀ M ≥ M0, ∀ m : ℕ, (M + 1) / 2 ≤ m →
      ∀ T : ℕ, paperScheduleX d m ≤ Real.log T → T0 ≤ T := by
  refine ⟨2 * T0, ?_⟩
  intro M hM m hm T hlog
  have hx := paperScheduleX_ge_count d m hd
  have hm0 : T0 ≤ m := by omega
  have hl : Real.log (T : ℝ) ≤ T := by
    by_cases hz : T = 0
    · simp [hz]
    · have hp : (0 : ℝ) < T := by exact_mod_cast Nat.pos_of_ne_zero hz
      linarith [Real.log_le_sub_one_of_pos hp]
  have hmR : (T0 : ℝ) ≤ m := by exact_mod_cast hm0
  exact_mod_cast (by linarith : (T0 : ℝ) ≤ T)

end BinaryFormMoat.GeometryIntegration

#print axioms BinaryFormMoat.GeometryIntegration.paperPrimeCount
#print axioms BinaryFormMoat.GeometryIntegration.paperPrimeCount_bounds
#print axioms BinaryFormMoat.GeometryIntegration.paperPrimeInventory_of_capacity
#print axioms BinaryFormMoat.GeometryIntegration.paperPrimeInventory_geometric_scales
#print axioms BinaryFormMoat.GeometryIntegration.paperPrimeAlphabet_budget
#print axioms BinaryFormMoat.GeometryIntegration.exists_paper_prime_inventory
#print axioms BinaryFormMoat.GeometryIntegration.paperSchedule_uniform_batch_threshold
