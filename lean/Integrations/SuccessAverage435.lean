import Integrations.SuccessEntropy435
import Mathlib.Analysis.Convex.Jensen

namespace BinaryFormMoat.EntropyIntegration

/-- Arithmetic mean over the specified coordinates, rather than a new
probability law or an average over conditioning fibers. -/
noncomputable def finiteRealMean {ι : Type*} (B : Finset ι) (f : ι → ℝ) : ℝ :=
  (∑ i ∈ B, f i) / (B.card : ℝ)

theorem concaveOn_successEntropyCost :
    ConcaveOn ℝ (Set.Icc (0 : ℝ) 1) successEntropyCost := by
  refine ⟨convex_Icc _ _, ?_⟩
  intro x hx y hy a b ha hb hab
  have h0 := Real.concaveOn_negMulLog.2 hx.1 hy.1 ha hb hab
  have h1 := Real.concaveOn_negMulLog.2
    (sub_nonneg.mpr hx.2) (sub_nonneg.mpr hy.2) ha hb hab
  simp only [smul_eq_mul] at h0 h1 ⊢
  have he : 1 - (a * x + b * y) = a * (1 - x) + b * (1 - y) := by
    nlinarith only [hab]
  unfold successEntropyCost
  rw [he]
  linarith only [h0, h1]

theorem finiteRealMean_mem_unitInterval {ι : Type*} (B : Finset ι)
    (hB : B.Nonempty) (a : ι → ℝ) (ha : ∀ i ∈ B, a i ∈ Set.Icc (0 : ℝ) 1) :
    finiteRealMean B a ∈ Set.Icc (0 : ℝ) 1 := by
  have hn : (0 : ℝ) < B.card := by exact_mod_cast hB.card_pos
  refine ⟨div_nonneg (Finset.sum_nonneg (fun i hi => (ha i hi).1)) hn.le, ?_⟩
  unfold finiteRealMean
  apply (div_le_one hn).mpr
  calc
    _ ≤ ∑ i ∈ B, (1 : ℝ) := Finset.sum_le_sum (fun i hi => (ha i hi).2)
    _ = _ := by simp

/-- Jensen uses the average success probability; individual successes
may vanish and may be correlated with all of the shared data. -/
theorem finiteRealMean_successEntropyCost_le {ι : Type*} (B : Finset ι)
    (hB : B.Nonempty) (a : ι → ℝ) (ha : ∀ i ∈ B, a i ∈ Set.Icc (0 : ℝ) 1) :
    finiteRealMean B (fun i => successEntropyCost (a i)) ≤
      successEntropyCost (finiteRealMean B a) := by
  have hn : (B.card : ℝ) ≠ 0 := by exact_mod_cast hB.card_ne_zero
  have hw : ∑ i ∈ B, (B.card : ℝ)⁻¹ = 1 := by simp [hn]
  have h := concaveOn_successEntropyCost.le_map_sum
    (fun i (_ : i ∈ B) => inv_nonneg.mpr (Nat.cast_nonneg B.card)) hw ha
  simp only [smul_eq_mul, ← Finset.mul_sum] at h
  simpa only [finiteRealMean, div_eq_mul_inv, mul_comm] using h

/-- Average all success-list certificates before paying Boolean entropy. -/
theorem finiteRealMean_deficit_ge_success {ι : Type*} (B : Finset ι)
    (hB : B.Nonempty) (a g D : ι → ℝ) (G : ℝ)
    (ha : ∀ i ∈ B, a i ∈ Set.Icc (0 : ℝ) 1)
    (hg : ∀ i ∈ B, G ≤ g i)
    (hD : ∀ i ∈ B, a i * g i - successEntropyCost (a i) ≤ D i) :
    finiteRealMean B a * G - successEntropyCost (finiteRealMean B a) ≤
      finiteRealMean B D := by
  have he := finiteRealMean_successEntropyCost_le B hB a ha
  have hs : ∑ i ∈ B, (a i * G - successEntropyCost (a i)) ≤ ∑ i ∈ B, D i := by
    apply Finset.sum_le_sum
    intro i hi
    have h := mul_le_mul_of_nonneg_left (hg i hi) (ha i hi).1
    linarith only [h, hD i hi]
  have h := div_le_div_of_nonneg_right hs (Nat.cast_nonneg B.card)
  simp only [Finset.sum_sub_distrib, ← Finset.sum_mul, sub_div] at h
  rw [mul_div_right_comm] at h
  change finiteRealMean B a * G -
    finiteRealMean B (fun i => successEntropyCost (a i)) ≤ finiteRealMean B D at h
  linarith only [h, he]

theorem successEntropyCost_le_of_success_floor (a m : ℝ)
    (hm : 0 < m) (hma : m ≤ a) (ha1 : a ≤ 1) :
    successEntropyCost a ≤ a * Real.log (Real.exp 1 / m) := by
  have ha : 0 < a := hm.trans_le hma
  apply (successEntropyCost_le_log_bound a ha ha1).trans
  apply mul_le_mul_of_nonneg_left _ ha.le
  apply Real.log_le_log (div_pos (Real.exp_pos 1) ha)
  exact div_le_div_of_nonneg_left (Real.exp_pos 1).le hm hma

/-- Scalar form of the source's last averaging step. The log threshold
and mean-success floor are explicit application inputs. -/
theorem finiteRealMean_deficit_ge_coverage_scale {ι : Type*} (B : Finset ι)
    (hB : B.Nonempty) (a g D : ι → ℝ) (δ β L : ℝ)
    (hδ : 0 < δ) (hβ : 0 ≤ β) (hL : 0 ≤ L)
    (ha : ∀ i ∈ B, a i ∈ Set.Icc (0 : ℝ) 1)
    (hmean : δ / 2 ≤ finiteRealMean B a)
    (hg : ∀ i ∈ B, β / 2 * L ≤ g i)
    (hD : ∀ i ∈ B, a i * g i - successEntropyCost (a i) ≤ D i)
    (hlog : Real.log (Real.exp 1 / (δ / 2)) ≤ β / 4 * L) :
    δ * β / 8 * L ≤ finiteRealMean B D := by
  have hav := finiteRealMean_mem_unitInterval B hB a ha
  have he := successEntropyCost_le_of_success_floor (finiteRealMean B a) (δ / 2)
    (half_pos hδ) hmean hav.2
  have hb := finiteRealMean_deficit_ge_success B hB a g D (β / 2 * L) ha hg hD
  have hl := mul_le_mul_of_nonneg_left hlog hav.1
  have hm : (δ / 2) * (β / 4 * L) ≤ finiteRealMean B a * (β / 4 * L) :=
    mul_le_mul_of_nonneg_right hmean
    (mul_nonneg (div_nonneg hβ (by norm_num)) hL)
  nlinarith only [he, hb, hl, hm]

end BinaryFormMoat.EntropyIntegration

#print axioms BinaryFormMoat.EntropyIntegration.concaveOn_successEntropyCost
#print axioms BinaryFormMoat.EntropyIntegration.finiteRealMean_mem_unitInterval
#print axioms BinaryFormMoat.EntropyIntegration.finiteRealMean_successEntropyCost_le
#print axioms BinaryFormMoat.EntropyIntegration.finiteRealMean_deficit_ge_success
#print axioms BinaryFormMoat.EntropyIntegration.successEntropyCost_le_of_success_floor
#print axioms BinaryFormMoat.EntropyIntegration.finiteRealMean_deficit_ge_coverage_scale
