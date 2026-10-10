import Integrations.WordBlocks435

namespace BinaryFormMoat.EntropyIntegration
open MeasureTheory ProbabilityTheory

/-- Finite normalized-rate telescope with a separate error for each
transition. The last conditional entropy is not discarded prematurely. -/
theorem rate_telescope (a b error : ℕ → ℝ) (n : ℕ)
    (hnext : ∀ i < n, a (i + 1) ≤ b i + error i) :
    (∑ i ∈ Finset.range (n + 1), (a i - b i)) ≤
      a 0 - b n + ∑ i ∈ Finset.range n, error i := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hp := ih (fun i hi => hnext i (by omega))
    have hn := hnext n (by omega)
    rw [Finset.sum_range_succ (fun i => a i - b i),
      Finset.sum_range_succ error]
    linarith

theorem rate_telescope_budget (a b error : ℕ → ℝ) (n : ℕ) (budget : ℝ)
    (hnext : ∀ i < n, a (i + 1) ≤ b i + error i)
    (hstart : a 0 ≤ budget) (hend : 0 ≤ b n) :
    (∑ i ∈ Finset.range (n + 1), (a i - b i)) ≤
      budget + ∑ i ∈ Finset.range n, error i := by
  have h := rate_telescope a b error n hnext
  linarith

theorem rate_telescope_uniform_budget (a b : ℕ → ℝ) (n : ℕ) (budget ε : ℝ)
    (hnext : ∀ i < n, a (i + 1) ≤ b i + ε)
    (hstart : a 0 ≤ budget) (hend : 0 ≤ b n) :
    (∑ i ∈ Finset.range (n + 1), (a i - b i)) ≤ budget + n * ε := by
  simpa only [Finset.sum_const, Finset.card_range, nsmul_eq_mul] using
    rate_telescope_budget a b (fun _ => ε) n budget hnext hstart hend

/-- Exact information divided by the current word length, which may vary
with the batch. All histories and words live on the same law. -/
theorem word_information_rate_eq {Ω K G : Type*}
    [MeasurableSpace Ω]
    [Fintype K] [MeasurableSpace K] [MeasurableSingletonClass K]
    [Fintype G] [MeasurableSpace G] [MeasurableSingletonClass G]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (L : ℕ → ℕ) (W : (i : ℕ) → Ω → (Fin (L i) → K))
    (hW : ∀ i, Measurable (W i)) (Y : ℕ → Ω → G)
    (hY : ∀ i, Measurable (Y i)) (i : ℕ) :
    condMutualInfo (Y i) (W i) (observationHistory Y i) μ / L i =
      condEntropy (W i) (observationHistory Y i) μ / L i -
        condEntropy (W i) (observationHistory Y (i + 1)) μ / L i := by
  rw [condMutualInfo_comm (hY i) (hW i) _ μ,
    information_observationHistory_step μ (W i) (hW i) Y hY i, sub_div]

theorem condEntropy_word_rate_le_log_card {Ω K U : Type*}
    [MeasurableSpace Ω]
    [Fintype K] [MeasurableSpace K] [MeasurableSingletonClass K]
    [MeasurableSpace U] [MeasurableSingletonClass U]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (L : ℕ) (hL : 0 < L)
    (W : Ω → (Fin L → K)) (Z : Ω → U) :
    condEntropy W Z μ / L ≤ Real.log (Fintype.card K) := by
  apply (div_le_iff₀ (Nat.cast_pos.mpr hL)).mpr
  have h := condEntropy_le_log_card W Z μ
  simpa only [Fintype.card_fun, Fintype.card_fin, Nat.cast_pow, Real.log_pow, mul_comm] using h

/-- Different lengths are charged by normalized entropy transitions, rather
than charging unnormalized information to one longest word. -/
theorem varying_word_information_budget {Ω K G : Type*}
    [MeasurableSpace Ω]
    [Fintype K] [MeasurableSpace K] [MeasurableSingletonClass K]
    [Fintype G] [MeasurableSpace G] [MeasurableSingletonClass G]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (L : ℕ → ℕ) (hL : ∀ i, 0 < L i)
    (W : (i : ℕ) → Ω → (Fin (L i) → K)) (hW : ∀ i, Measurable (W i))
    (Y : ℕ → Ω → G) (hY : ∀ i, Measurable (Y i)) (error : ℕ → ℝ) (n : ℕ)
    (hnext : ∀ i < n,
      condEntropy (W (i + 1)) (observationHistory Y (i + 1)) μ / L (i + 1) ≤
        condEntropy (W i) (observationHistory Y (i + 1)) μ / L i + error i) :
    (∑ i ∈ Finset.range (n + 1),
      condMutualInfo (Y i) (W i) (observationHistory Y i) μ / L i) ≤
      Real.log (Fintype.card K) + ∑ i ∈ Finset.range n, error i := by
  simp_rw [word_information_rate_eq μ L W hW Y hY]
  apply rate_telescope_budget
    (fun i => condEntropy (W i) (observationHistory Y i) μ / L i)
    (fun i => condEntropy (W i) (observationHistory Y (i + 1)) μ / L i)
    error n (Real.log (Fintype.card K)) hnext
  · exact condEntropy_word_rate_le_log_card μ (L 0) (hL 0) (W 0) _
  · exact div_nonneg (condEntropy_nonneg _ _ _) (Nat.cast_nonneg _)

/-- Additive reconstruction also applies to the entire finite residue
history; it keeps every previously exposed residue coordinate. -/
theorem observationHistory_residue_step {K G : Type*} [AddCommMonoid G]
    (w : ℕ → K) (contribution : ℕ → K → G) (Y : ℕ → ℕ → G)
    (hstep : ∀ i t, Y i (t + 1) = Y i t + contribution i (w t)) (n t : ℕ) :
    observationHistory Y n (t + 1) =
      observationHistory Y n t + observationHistory contribution n (w t) := by
  induction n with
  | zero => funext i; exact Fin.elim0 i
  | succ n ih =>
    funext i
    cases i using Fin.cases with
    | zero => exact hstep n t
    | succ i => exact congrFun ih i

/-- Common-law budget for actual consecutive block lengths and additive
residue observations, with the proved terminal-smoothing error. -/
theorem smoothedTimeLaw_varying_word_information_budget {Ω K G : Type*}
    [Fintype Ω] [MeasurableSpace Ω] [MeasurableSingletonClass Ω]
    [Fintype K] [MeasurableSpace K] [MeasurableSingletonClass K]
    [Fintype G] [AddCommMonoid G] [MeasurableSpace G] [MeasurableSingletonClass G]
    [MeasurableSpace Bool] [MeasurableSingletonClass Bool]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (b : Ω → ℕ) (N : ℕ) [NeZero N]
    (w : ℕ → K) (contribution : ℕ → K → G) (Y : ℕ → ℕ → G)
    (hstep : ∀ i t, Y i (t + 1) = Y i t + contribution i (w t))
    (L B : ℕ → ℕ) (hL : ∀ i, 0 < L i) (n : ℕ)
    (hB : ∀ i < n, 0 < B i) (hblock : ∀ i < n, L (i + 1) = B i * L i)
    (T : ℝ) (hT : 1 ≤ T) (hlong : ∀ i < n, (L (i + 1) : ℝ) ≤ T)
    (hN : T ^ 10 ≤ (N : ℝ)) :
    (∑ i ∈ Finset.range (n + 1),
      condMutualInfo (Y i) (wordAt w (L i)) (observationHistory Y i)
        (smoothedTimeLaw μ b N) / L i) ≤
      Real.log (Fintype.card K) +
        ∑ i ∈ Finset.range n,
          ((1 + 9 * Real.log T + L i * Real.log (Fintype.card K)) / T ^ 9) / L i := by
  apply varying_word_information_budget (smoothedTimeLaw μ b N) L hL
    (fun i => wordAt w (L i)) (fun _ => measurable_of_countable _)
    Y (fun _ => measurable_of_countable _)
  intro i hi
  have h := smoothedTimeLaw_word_block_rate μ b N w
    (observationHistory contribution (i + 1)) (observationHistory Y (i + 1))
    (fun t => observationHistory_residue_step w contribution Y hstep (i + 1) t)
    (B i) (L i) (hB i hi) (hL i) T hT
    (by rw [← hblock i hi]; exact hlong i hi) hN
  rw [hblock i hi]
  exact h

/-- Normalizing before estimating removes the word length from the
continuity cost. Only the positive integer length is needed. -/
theorem normalized_smoothing_cost_le (L : ℕ) (hL : 0 < L) (T C : ℝ) (hT : 1 ≤ T) :
    ((1 + 9 * Real.log T + L * C) / T ^ 9) / L ≤
      (1 + 9 * Real.log T + C) / T ^ 9 := by
  have hLr : (0 : ℝ) < L := Nat.cast_pos.mpr hL
  have hL1 : (1 : ℝ) ≤ L := by exact_mod_cast hL
  have hA : 0 ≤ 1 + 9 * Real.log T := by
    have hl := Real.log_nonneg hT
    linarith
  have he : ((1 + 9 * Real.log T + L * C) / T ^ 9) / L =
      ((1 + 9 * Real.log T + L * C) / L) / T ^ 9 := by ring
  rw [he]
  apply div_le_div_of_nonneg_right _ (pow_nonneg (by linarith : 0 ≤ T) 9)
  apply (div_le_iff₀ hLr).mpr
  nlinarith [mul_le_mul_of_nonneg_left hL1 hA]

theorem smoothedTimeLaw_varying_word_uniform_budget {Ω K G : Type*}
    [Fintype Ω] [MeasurableSpace Ω] [MeasurableSingletonClass Ω]
    [Fintype K] [MeasurableSpace K] [MeasurableSingletonClass K]
    [Fintype G] [AddCommMonoid G] [MeasurableSpace G] [MeasurableSingletonClass G]
    [MeasurableSpace Bool] [MeasurableSingletonClass Bool]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (b : Ω → ℕ) (N : ℕ) [NeZero N]
    (w : ℕ → K) (contribution : ℕ → K → G) (Y : ℕ → ℕ → G)
    (hstep : ∀ i t, Y i (t + 1) = Y i t + contribution i (w t))
    (L B : ℕ → ℕ) (hL : ∀ i, 0 < L i) (n : ℕ)
    (hB : ∀ i < n, 0 < B i) (hblock : ∀ i < n, L (i + 1) = B i * L i)
    (T : ℝ) (hT : 1 ≤ T) (hlong : ∀ i < n, (L (i + 1) : ℝ) ≤ T)
    (hN : T ^ 10 ≤ (N : ℝ)) :
    (∑ i ∈ Finset.range (n + 1),
      condMutualInfo (Y i) (wordAt w (L i)) (observationHistory Y i)
        (smoothedTimeLaw μ b N) / L i) ≤
      Real.log (Fintype.card K) +
        n * ((1 + 9 * Real.log T + Real.log (Fintype.card K)) / T ^ 9) := by
  have h := smoothedTimeLaw_varying_word_information_budget μ b N w contribution Y hstep
    L B hL n hB hblock T hT hlong hN
  apply h.trans
  apply add_le_add le_rfl
  have hs := Finset.sum_le_sum (s := Finset.range n)
    (fun i _ => normalized_smoothing_cost_le (L i) (hL i) T
      (Real.log (Fintype.card K)) hT)
  simpa only [Finset.sum_const, Finset.card_range, nsmul_eq_mul] using hs

end BinaryFormMoat.EntropyIntegration

#print axioms BinaryFormMoat.EntropyIntegration.rate_telescope
#print axioms BinaryFormMoat.EntropyIntegration.rate_telescope_budget
#print axioms BinaryFormMoat.EntropyIntegration.rate_telescope_uniform_budget
#print axioms BinaryFormMoat.EntropyIntegration.word_information_rate_eq
#print axioms BinaryFormMoat.EntropyIntegration.condEntropy_word_rate_le_log_card
#print axioms BinaryFormMoat.EntropyIntegration.varying_word_information_budget
#print axioms BinaryFormMoat.EntropyIntegration.observationHistory_residue_step
#print axioms BinaryFormMoat.EntropyIntegration.smoothedTimeLaw_varying_word_information_budget
#print axioms BinaryFormMoat.EntropyIntegration.normalized_smoothing_cost_le
#print axioms BinaryFormMoat.EntropyIntegration.smoothedTimeLaw_varying_word_uniform_budget
