import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

namespace BinaryFormMoat
open Filter
open scoped Topology

/-- The prime-counting scale grows without bound. -/
theorem tendsto_primeCountingScale :
    Tendsto (fun x : ℝ => x / Real.log x) atTop atTop := by
  have hzero : Tendsto (fun x : ℝ => Real.log x / x) atTop (𝓝 0) :=
    Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero
  have hpos : ∀ᶠ x : ℝ in atTop, 0 < Real.log x / x := by
    filter_upwards [eventually_gt_atTop (1 : ℝ)] with x hx
    exact div_pos (Real.log_pos hx) (by linarith)
  have hr : Tendsto (fun x : ℝ => Real.log x / x) atTop (𝓝[>] 0) :=
    tendsto_nhdsWithin_iff.mpr ⟨hzero, hpos⟩
  have hi := hr.inv_tendsto_nhdsGT_zero
  change Tendsto (fun x : ℝ => (Real.log x / x)⁻¹) atTop atTop at hi
  simpa only [inv_div] using hi

/-- The logarithm changes by an asymptotically negligible factor on doubling intervals. -/
theorem tendsto_log_div_log_double :
    Tendsto (fun x : ℝ => Real.log x / Real.log (2 * x)) atTop (𝓝 1) := by
  have hsmall : Tendsto (fun x : ℝ => Real.log 2 / Real.log x) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop Real.tendsto_log_atTop
  have hone : Tendsto (fun _ : ℝ => (1 : ℝ)) atTop (𝓝 1) := tendsto_const_nhds
  have h := hone.div (hone.add hsmall)
    (by norm_num : (1 : ℝ) + 0 ≠ 0)
  have hh : Tendsto (fun x : ℝ => 1 / (1 + Real.log 2 / Real.log x)) atTop (𝓝 1) := by
    change Tendsto (fun x : ℝ => 1 / (1 + Real.log 2 / Real.log x))
      atTop (𝓝 (1 / (1 + 0))) at h
    simpa only [add_zero, div_one] using h
  apply hh.congr'
  filter_upwards [eventually_gt_atTop (1 : ℝ)] with x hx
  have hlog : Real.log x ≠ 0 := ne_of_gt (Real.log_pos hx)
  rw [Real.log_mul (by norm_num) (by linarith : x ≠ 0)]
  field_simp [hlog]
  ring

/-- A Chebotarev-shaped counting asymptotic supplies the same density on (x,2x].
This is a generic analytic bridge: the arithmetic counting theorem is an explicit input. -/
theorem tendsto_dyadic_count (C : ℝ → ℝ) (δ : ℝ)
    (hC : Tendsto (fun x : ℝ => C x / (x / Real.log x)) atTop (𝓝 δ)) :
    Tendsto (fun x : ℝ => (C (2 * x) - C x) / (x / Real.log x)) atTop (𝓝 δ) := by
  have hd : Tendsto (fun x : ℝ => 2 * x) atTop atTop :=
    tendsto_id.const_mul_atTop (by norm_num)
  have hscaled := ((hC.comp hd).mul_const 2).mul tendsto_log_div_log_double
  have hscaled' : Tendsto (fun x : ℝ => C (2 * x) / (x / Real.log x)) atTop (𝓝 (2 * δ)) := by
    convert hscaled.congr' ?_ using 1
    · simp [mul_comm]
    filter_upwards [eventually_gt_atTop (1 : ℝ)] with x hx
    have hx0 : x ≠ 0 := by linarith
    have hl : Real.log (2 * x) ≠ 0 := ne_of_gt (Real.log_pos (by linarith))
    dsimp [Function.comp_def]
    field_simp
  simpa only [← sub_div, show 2 * δ - δ = δ by ring] using hscaled'.sub hC

/-- Discarding any fixed finite exceptional budget preserves a positive dyadic supply. -/
theorem eventually_dyadic_supply (C : ℝ → ℝ) (δ B : ℝ) (hδ : 0 < δ)
    (hC : Tendsto (fun x : ℝ => C x / (x / Real.log x)) atTop (𝓝 δ)) :
    ∀ᶠ x : ℝ in atTop,
      (δ / 2) * (x / Real.log x) ≤ C (2 * x) - C x - B := by
  have hb : Tendsto (fun x : ℝ => B / (x / Real.log x)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop tendsto_primeCountingScale
  have h : Tendsto (fun x : ℝ => (C (2 * x) - C x - B) / (x / Real.log x))
      atTop (𝓝 δ) := by
    simpa only [← sub_div, sub_zero] using (tendsto_dyadic_count C δ hC).sub hb
  filter_upwards [h.eventually (lt_mem_nhds (show δ / 2 < δ by linarith)),
    eventually_gt_atTop (1 : ℝ)] with x hx hx1
  exact le_of_lt ((lt_div_iff₀ (div_pos (by linarith) (Real.log_pos hx1))).mp hx)

/-- Even after finite exclusions, a sufficiently distant doubling interval meets any finite quota. -/
theorem eventually_dyadic_quota (C : ℝ → ℝ) (δ B N : ℝ) (hδ : 0 < δ)
    (hC : Tendsto (fun x : ℝ => C x / (x / Real.log x)) atTop (𝓝 δ)) :
    ∀ᶠ x : ℝ in atTop, N ≤ C (2 * x) - C x - B := by
  have hg : Tendsto (fun x : ℝ => (δ / 2) * (x / Real.log x)) atTop atTop :=
    tendsto_primeCountingScale.const_mul_atTop (by linarith)
  filter_upwards [hg.eventually_ge_atTop N, eventually_dyadic_supply C δ B hδ hC] with x hx hbound
  exact hx.trans hbound

/-- The full available batch retains a quantitative lower bound proportional to x/log x. -/
theorem eventually_dyadic_card_lower_bound {α : Type*} [DecidableEq α]
    (S : ℝ → Finset α) (δ : ℝ) (hδ : 0 < δ)
    (hS : Tendsto (fun x : ℝ => (S x).card / (x / Real.log x)) atTop (𝓝 δ))
    (bad : Finset α) :
    ∀ᶠ x : ℝ in atTop,
      (δ / 2) * (x / Real.log x) ≤ (((S (2 * x) \ S x) \ bad).card : ℝ) := by
  filter_upwards [eventually_dyadic_supply (fun x => (S x).card) δ bad.card hδ hS] with x hx
  have h₁ : (S (2 * x)).card ≤ (S (2 * x) \ S x).card + (S x).card :=
    Finset.card_le_card_sdiff_add_card
  have h₂ : (S (2 * x) \ S x).card ≤ ((S (2 * x) \ S x) \ bad).card + bad.card :=
    Finset.card_le_card_sdiff_add_card
  have h₁' : ((S (2 * x)).card : ℝ) ≤ (S (2 * x) \ S x).card + (S x).card := by
    exact_mod_cast h₁
  have h₂' : ((S (2 * x) \ S x).card : ℝ) ≤ ((S (2 * x) \ S x) \ bad).card + bad.card := by
    exact_mod_cast h₂
  linarith

/-- Convert the counting asymptotic into actual finite batches, with a prescribed cardinality
and disjoint from any fixed finite bad set. No selection algorithm or count oracle is trusted. -/
theorem eventually_exists_dyadic_batch {α : Type*} [DecidableEq α]
    (S : ℝ → Finset α) (δ : ℝ) (hδ : 0 < δ)
    (hS : Tendsto (fun x : ℝ => (S x).card / (x / Real.log x)) atTop (𝓝 δ))
    (bad : Finset α) (N : ℕ) :
    ∀ᶠ x : ℝ in atTop, ∃ T : Finset α,
      T ⊆ S (2 * x) \ S x ∧ Disjoint T bad ∧ T.card = N := by
  filter_upwards [eventually_dyadic_quota (fun x => (S x).card) δ bad.card N hδ hS] with x hx
  have h₁ : (S (2 * x)).card ≤ (S (2 * x) \ S x).card + (S x).card :=
    Finset.card_le_card_sdiff_add_card
  have h₂ : (S (2 * x) \ S x).card ≤ ((S (2 * x) \ S x) \ bad).card + bad.card :=
    Finset.card_le_card_sdiff_add_card
  have hsize : N ≤ ((S (2 * x) \ S x) \ bad).card := by
    have h₁' : ((S (2 * x)).card : ℝ) ≤ (S (2 * x) \ S x).card + (S x).card := by
      exact_mod_cast h₁
    have h₂' : ((S (2 * x) \ S x).card : ℝ) ≤ ((S (2 * x) \ S x) \ bad).card + bad.card := by
      exact_mod_cast h₂
    have hh : (N : ℝ) ≤ ((S (2 * x) \ S x) \ bad).card := by linarith
    exact_mod_cast hh
  obtain ⟨T, hT, hcard⟩ := Finset.exists_subset_card_eq hsize
  refine ⟨T, hT.trans Finset.sdiff_subset, ?_, hcard⟩
  exact Finset.disjoint_left.mpr (fun _ ht hb => (Finset.mem_sdiff.mp (hT ht)).2 hb)

end BinaryFormMoat
