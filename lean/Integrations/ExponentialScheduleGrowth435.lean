import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity

namespace BinaryFormMoat.GeometryIntegration
open Filter
open scoped Topology

/-- A positive exponential dominates a polynomial plus a linear term. -/
theorem tendsto_exponential_polynomial_gap (a c b k : ℝ) (n : ℕ)
    (ha : 0 < a) (hc : 0 < c) :
    Tendsto (fun x : ℝ => c * Real.exp (a * x) - b * x ^ n - k * x) atTop atTop := by
  have hp := ((isLittleO_pow_exp_pos_mul_atTop n ha).tendsto_div_nhds_zero).const_mul b
  have hlin := ((isLittleO_pow_exp_pos_mul_atTop 1 ha).tendsto_div_nhds_zero).const_mul k
  have hzero : Tendsto (fun x : ℝ => (b * x ^ n + k * x) / Real.exp (a * x)) atTop (𝓝 0) := by
    convert hp.add hlin using 1 <;> simp only [mul_zero, add_zero, pow_one]
    ext x
    ring
  have hgrowth : Tendsto (fun x : ℝ => (c / 2) * Real.exp (a * x)) atTop atTop :=
    (Real.tendsto_exp_atTop.comp (tendsto_id.const_mul_atTop ha)).const_mul_atTop (by positivity)
  apply tendsto_atTop_mono' atTop _ hgrowth
  filter_upwards [hzero.eventually (gt_mem_nhds (show (0 : ℝ) < c / 2 by positivity))] with x hx
  have h := (div_lt_iff₀ (Real.exp_pos (a * x))).mp hx
  linarith

/-- The double exponential scale wins even after polynomially small slack
and an exponential upper batch scale have both been charged. -/
theorem tendsto_double_exponential_ratio (a c b k : ℝ) (n : ℕ)
    (ha : 0 < a) (hc : 0 < c) :
    Tendsto (fun x : ℝ => Real.exp (-b * x ^ n) * Real.exp (c * Real.exp (a * x)) /
      Real.exp (k * x)) atTop atTop := by
  have h := Real.tendsto_exp_atTop.comp (tendsto_exponential_polynomial_gap a c b k n ha hc)
  apply h.congr
  intro x
  dsimp [Function.comp_def]
  rw [← Real.exp_add, ← Real.exp_sub]
  congr 1
  ring

end BinaryFormMoat.GeometryIntegration

#print axioms BinaryFormMoat.GeometryIntegration.tendsto_exponential_polynomial_gap
#print axioms BinaryFormMoat.GeometryIntegration.tendsto_double_exponential_ratio
