import Integrations.OneStepCoverage435

noncomputable section
namespace BinaryFormMoat.EntropyIntegration
open MeasureTheory ProbabilityTheory

/-- Scalar contribution to the entropy deficit relative to a uniform law. -/
def entropyDensityDeficit (x : ℝ) : ℝ := x * Real.log x + 1 - x

theorem entropyDensityDeficit_nonneg (x : ℝ) (hx : 0 ≤ x) :
    0 ≤ entropyDensityDeficit x := by
  have h := Real.negMulLog_le_one_sub_self hx
  unfold entropyDensityDeficit Real.negMulLog at *
  linarith

/-- A coarse global bound obtained from the tangent inequality at 2*x.
No calculus, general Pinsker inequality or KL-divergence library is needed. -/
theorem negMulLog_le_half (x : ℝ) (hx : 0 ≤ x) : Real.negMulLog x ≤ 1 / 2 := by
  by_cases hz : x = 0
  · subst x; simp
  have h := Real.negMulLog_le_one_sub_self (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hx)
  have hl : Real.log (2 : ℝ) ≤ 1 := by
    convert Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2) using 1
    norm_num
  rw [Real.negMulLog, Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) hz] at h
  unfold Real.negMulLog
  nlinarith [mul_le_mul_of_nonneg_left hl hx]

/-- Each residue below 3/8 of its uniform mass pays at least 1/8
in normalized scalar entropy deficit. -/
theorem entropyDensityDeficit_ge_eighth (x : ℝ) (hx : 0 ≤ x) (hsmall : x ≤ 3 / 8) :
    1 / 8 ≤ entropyDensityDeficit x := by
  have h := negMulLog_le_half x hx
  unfold entropyDensityDeficit Real.negMulLog at *
  linarith

theorem sum_residue_mass_eq_one {Ω G : Type*} [MeasurableSpace Ω]
    [Fintype G] [MeasurableSpace G] [MeasurableSingletonClass G]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (Z : Ω → G) (hZ : Measurable Z) :
    (∑ u, μ.real (Z ⁻¹' {u})) = 1 := by
  classical
  have h := sum_measureReal_preimage_singleton (μ := μ) (Finset.univ : Finset G)
    (fun u _ => hZ (MeasurableSet.singleton u))
  simpa using h

/-- Exact finite density-deficit identity, including zero-mass residues. -/
theorem sum_entropyDensityDeficit_eq {Ω G : Type*} [MeasurableSpace Ω]
    [Fintype G] [Nonempty G] [MeasurableSpace G] [MeasurableSingletonClass G]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (Z : Ω → G) (hZ : Measurable Z) :
    (∑ u, entropyDensityDeficit ((Fintype.card G : ℝ) * μ.real (Z ⁻¹' {u}))) =
      (Fintype.card G : ℝ) * (Real.log (Fintype.card G) - entropy Z μ) := by
  classical
  let n : ℝ := Fintype.card G
  let p := fun u => μ.real (Z ⁻¹' {u})
  have hn : 0 < n := by
    dsimp only [n]
    exact_mod_cast (Fintype.card_pos : 0 < Fintype.card G)
  have hsum : ∑ u, p u = 1 := sum_residue_mass_eq_one μ Z hZ
  have hpoint : ∀ u, entropyDensityDeficit (n * p u) =
      n * p u * Real.log n - n * Real.negMulLog (p u) + 1 - n * p u := by
    intro u
    by_cases hz : p u = 0
    · simp [hz, entropyDensityDeficit]
    · rw [entropyDensityDeficit, Real.log_mul hn.ne' hz, Real.negMulLog]
      ring
  have he : entropy Z μ = ∑ u, Real.negMulLog (p u) := by
    rw [entropy_eq_sum μ, tsum_fintype]
    simp only [map_measureReal_apply hZ (MeasurableSet.singleton _), p]
  change (∑ u, entropyDensityDeficit (n * p u)) = n * (Real.log n - entropy Z μ)
  simp_rw [hpoint]
  simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.mul_sum,
    ← Finset.sum_mul, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one]
  rw [hsum, ← he]
  dsimp only [n]
  ring

/-- Direct rare-residue bound, stronger than the squared-total-variation
estimate required by the manuscript's terminal base case. -/
theorem lowProbabilityResidues_card_le_entropy_deficit {Ω G : Type*} [MeasurableSpace Ω]
    [Fintype G] [Nonempty G] [MeasurableSpace G] [MeasurableSingletonClass G]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (Z : Ω → G) (hZ : Measurable Z)
    (τ : ℝ) (hτ : τ ≤ 3 / 8) :
    ((lowProbabilityResidues μ Z τ).card : ℝ) /
      (8 * Fintype.card G) ≤ Real.log (Fintype.card G) - entropy Z μ := by
  classical
  let B := lowProbabilityResidues μ Z τ
  let n : ℝ := Fintype.card G
  have hn : 0 < n := by
    dsimp only [n]
    exact_mod_cast (Fintype.card_pos : 0 < Fintype.card G)
  have hB : (B.card : ℝ) / 8 ≤
      ∑ u ∈ B, entropyDensityDeficit (n * μ.real (Z ⁻¹' {u})) := by
    calc
      _ = ∑ _u ∈ B, (1 / 8 : ℝ) := by simp; ring
      _ ≤ _ := Finset.sum_le_sum fun u hu => by
        apply entropyDensityDeficit_ge_eighth _ (mul_nonneg hn.le measureReal_nonneg)
        have hm := ((mem_lowProbabilityResidues μ Z τ u).mp hu).le
        have hm' : n * μ.real (Z ⁻¹' {u}) ≤ τ := by
          have := (le_div_iff₀ hn).mp hm
          nlinarith
        exact hm'.trans hτ
  have hu : ∑ u ∈ B, entropyDensityDeficit (n * μ.real (Z ⁻¹' {u})) ≤
      ∑ u, entropyDensityDeficit (n * μ.real (Z ⁻¹' {u})) :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ B)
      (fun u _ _ => entropyDensityDeficit_nonneg _ (mul_nonneg hn.le measureReal_nonneg))
  have ht := hB.trans hu
  rw [sum_entropyDensityDeficit_eq μ Z hZ] at ht
  apply (div_le_iff₀ (mul_pos (by norm_num) hn)).mpr
  change (B.card : ℝ) ≤ (Real.log n - entropy Z μ) * (8 * n)
  nlinarith

end BinaryFormMoat.EntropyIntegration
#print axioms BinaryFormMoat.EntropyIntegration.entropyDensityDeficit
#print axioms BinaryFormMoat.EntropyIntegration.entropyDensityDeficit_nonneg
#print axioms BinaryFormMoat.EntropyIntegration.negMulLog_le_half
#print axioms BinaryFormMoat.EntropyIntegration.entropyDensityDeficit_ge_eighth
#print axioms BinaryFormMoat.EntropyIntegration.sum_residue_mass_eq_one
#print axioms BinaryFormMoat.EntropyIntegration.sum_entropyDensityDeficit_eq
#print axioms BinaryFormMoat.EntropyIntegration.lowProbabilityResidues_card_le_entropy_deficit
