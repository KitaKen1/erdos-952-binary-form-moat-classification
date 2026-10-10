import Integrations.PaperJointInformationAverage435

noncomputable section
namespace BinaryFormMoat.GeometryIntegration
open EntropyIntegration

/-- The small degree-dependent beta gain survives the ACTUAL dyadic
bad-loss factor and fixed list cost. All losses have retained beta. -/
theorem beta_joint_numerator_margin (β δ ε s Λ U : ℝ)
    (hβ : 0 ≤ β) (hs : 0 ≤ s) (hΛ : 0 ≤ Λ)
    (haccuracy : δ + ε ≤ β / 4) (hgap : Real.log 6 ≤ β * Λ / 8)
    (hdyadic : U ≤ 2 * Λ) :
    β / 2 * (s * Λ) ≤ (β - δ - ε) * (s * Λ) - s * Real.log 6 -
      2 * paperCoverageEta 0 * s * U * β := by
  have hA := mul_le_mul_of_nonneg_right haccuracy (mul_nonneg hs hΛ)
  have hG := mul_le_mul_of_nonneg_left hgap hs
  have hB := mul_le_mul_of_nonneg_left hdyadic (mul_nonneg hs hβ)
  have hpos := mul_nonneg hβ (mul_nonneg hs hΛ)
  norm_num [paperCoverageEta] at ⊢
  nlinarith only [hA, hG, hB, hpos]

/-- Work backwards from the desired word-normalized rate. The original
joint numerator is divided by ONE actual common package quota. -/
theorem joint_quota_inverse_log_rate (β c T L K m logT n : ℝ)
    (hβ : 0 ≤ β) (hc : 0 ≤ c) (hT : 0 < T) (hL : 0 < L)
    (hK : 0 < K) (hm : 0 < m) (hlog : 0 < logT)
    (hquota : m ≤ 2 * K * (T / L) * logT) (hnum : β / 2 * (c * T) ≤ n) :
    β * c * L / (4 * K * logT) ≤ n / m := by
  apply (le_div_iff₀ hm).mpr
  have hpos : 0 ≤ β * c * L / (4 * K * logT) := by positivity
  calc
    _ ≤ (β * c * L / (4 * K * logT)) * (2 * K * (T / L) * logT) :=
      mul_le_mul_of_nonneg_left hquota hpos
    _ = β / 2 * (c * T) := by field_simp; ring
    _ ≤ n := hnum

/-- The physical loss must be absorbed ONCE per batch. This conditional
scalar helper does not supply the uniform physical threshold itself. -/
theorem joint_quota_transport_normalized_rate (β c T L K m logT n C I : ℝ)
    (hβ : 0 ≤ β) (hc : 0 ≤ c) (hT : 0 < T) (hL : 0 < L)
    (hK : 0 < K) (hm : 0 < m) (hlog : 0 < logT)
    (hquota : m ≤ 2 * K * (T / L) * logT) (hnum : β / 2 * (c * T) ≤ n)
    (hphysical : C ≤ β * c * L / (8 * K * logT)) (hinfo : n / m - C ≤ I) :
    β * c / (8 * K * logT) ≤ I / L := by
  have h := joint_quota_inverse_log_rate β c T L K m logT n hβ hc hT hL hK hm hlog hquota hnum
  apply (le_div_iff₀ hL).mpr
  have he : β * c / (8 * K * logT) * L = β * c * L / (8 * K * logT) := by ring
  rw [he]
  have he₂ : β * c * L / (4 * K * logT) = 2 * (β * c * L / (8 * K * logT)) := by ring
  rw [he₂] at h
  linarith

end BinaryFormMoat.GeometryIntegration
#print axioms BinaryFormMoat.GeometryIntegration.beta_joint_numerator_margin
#print axioms BinaryFormMoat.GeometryIntegration.joint_quota_inverse_log_rate
#print axioms BinaryFormMoat.GeometryIntegration.joint_quota_transport_normalized_rate
