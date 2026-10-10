import Integrations.JointInformationMargin435
import Integrations.DyadicRootWords435
import Integrations.PaperCheckpointScales435
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

noncomputable section
open scoped Topology
namespace BinaryFormMoat.GeometryIntegration
open Filter EntropyIntegration

/-- A positive power gap pays the physical cost uniformly BEFORE choosing
any word, prime set, walk or probability law. -/
theorem power_gap_uniform_physical_margin (a C ρ : ℝ) (ha : 0 < a)
    (_hC : 0 ≤ C) (hρ : 0 < ρ) :
    ∃ T0 : ℕ, 2 ≤ T0 ∧ ∀ T : ℕ, T0 ≤ T → ∀ L : ℝ,
      (T : ℝ) ^ (2 * a) ≤ 2 * L →
        C * (T : ℝ) ^ a ≤ ρ * L / Real.log T := by
  have ht := (isLittleO_log_rpow_atTop ha).tendsto_div_nhds_zero
  have htC := (ht.const_mul (2 * C)).comp tendsto_natCast_atTop_atTop
  have hev : ∀ᶠ T : ℕ in atTop, 2 * C * (Real.log T / (T : ℝ) ^ a) < ρ :=
    htC.eventually (gt_mem_nhds (by simpa using hρ))
  obtain ⟨N, hN⟩ := hev.exists_forall_of_atTop
  refine ⟨max N 2, le_max_right _ _, ?_⟩
  intro T hT L hL
  have hT₂ : 2 ≤ T := (le_max_right N 2).trans hT
  have hTp : (0 : ℝ) < T := by exact_mod_cast (by omega : 0 < T)
  have hlog : 0 < Real.log T := Real.log_pos (by exact_mod_cast hT₂)
  have hp : 0 < (T : ℝ) ^ a := Real.rpow_pos_of_pos hTp _
  have hs : 2 * C * Real.log T ≤ ρ * (T : ℝ) ^ a := by
    have h := (hN T ((le_max_left N 2).trans hT)).le
    rw [← mul_div_assoc] at h
    exact (div_le_iff₀ hp).mp h
  have hm := mul_le_mul_of_nonneg_right hs hp.le
  have hh := mul_le_mul_of_nonneg_left hL hρ.le
  have he : (T : ℝ) ^ a * (T : ℝ) ^ a = (T : ℝ) ^ (2 * a) := by
    rw [← Real.rpow_add hTp]
    congr 1
    ring
  rw [mul_assoc ρ, he] at hm
  apply (le_div_iff₀ hlog).mpr
  nlinarith only [hm, hh]

/-- The actual integer dyadic word supplies the real power comparison.
No real-log floor identity or supplied length asymptotic is required. -/
theorem rootWordLength_double_radius_lower (d T : ℕ) (hd : 1 ≤ d) :
    (T : ℝ) ^ (2 * paperCheckpointRadius d 0) ≤ 2 * rootWordLength d T := by
  have hdR : (0 : ℝ) < d := by exact_mod_cast (by omega : 0 < d)
  have he : 2 * paperCheckpointRadius d 0 = (((2 * d : ℕ) : ℝ))⁻¹ := by
    simp only [paperCheckpointRadius, pow_zero, sub_self, zero_div, sub_zero]
    push_cast
    field_simp
    ring
  rw [he]
  apply (Real.rpow_inv_le_iff_of_pos (Nat.cast_nonneg T)
    (by positivity : (0 : ℝ) ≤ 2 * rootWordLength d T)
    (by positivity : (0 : ℝ) < ((2 * d : ℕ) : ℝ))).mpr
  rw [Real.rpow_natCast]
  exact_mod_cast (rootWordLength_next_power_gt d T hd).le

/-- All actual dyadic words absorb a fixed physical alphabet cost using
one source-independent threshold. This supplies an asymptotic scalar margin;
the actual checkpoint cost still has to be bounded by C*T^radius. -/
theorem rootWordLength_uniform_physical_margin (d : ℕ) (hd : 1 ≤ d)
    (C ρ : ℝ) (hC : 0 ≤ C) (hρ : 0 < ρ) :
    ∃ T0 : ℕ, 2 ≤ T0 ∧ ∀ T : ℕ, T0 ≤ T →
      C * (T : ℝ) ^ paperCheckpointRadius d 0 ≤
        ρ * rootWordLength d T / Real.log T := by
  have hdR : (0 : ℝ) < d := by exact_mod_cast (by omega : 0 < d)
  have hr : 0 < paperCheckpointRadius d 0 := by rw [paperCheckpointRadius_zero]; positivity
  obtain ⟨T0, hT0, h⟩ := power_gap_uniform_physical_margin
    (paperCheckpointRadius d 0) C ρ hr hC hρ
  exact ⟨T0, hT0, fun T hT => h T hT _ (rootWordLength_double_radius_lower d T hd)⟩

end BinaryFormMoat.GeometryIntegration
#print axioms BinaryFormMoat.GeometryIntegration.power_gap_uniform_physical_margin
#print axioms BinaryFormMoat.GeometryIntegration.rootWordLength_double_radius_lower
#print axioms BinaryFormMoat.GeometryIntegration.rootWordLength_uniform_physical_margin
