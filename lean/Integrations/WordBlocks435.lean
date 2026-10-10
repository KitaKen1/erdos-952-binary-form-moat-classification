import Integrations.ConditionalBlocks435
import Integrations.SmoothingBudget435

namespace BinaryFormMoat.EntropyIntegration
open MeasureTheory ProbabilityTheory

def wordAt {K : Type*} (w : ℕ → K) (L : ℕ) (t : ℕ) : Fin L → K :=
  fun i => w (t + i)

def wordBlock {K : Type*} (w : ℕ → K) (L i t : ℕ) : Fin L → K :=
  wordAt w L (t + i * L)

/-- Exact partition of a flat word into chronological equal-length blocks. -/
def splitWord {K : Type*} (B L : ℕ) (w : Fin (B * L) → K) : Fin B → Fin L → K :=
  fun i j => w (finProdFinEquiv (i, j))

theorem splitWord_injective {K : Type*} (B L : ℕ) :
    Function.Injective (splitWord (K := K) B L) := by
  intro w v h
  funext j
  obtain ⟨⟨i, k⟩, rfl⟩ := finProdFinEquiv.surjective j
  exact congrFun (congrFun h i) k

theorem blockPrefix_wordBlock_eq_split {K : Type*} (w : ℕ → K) (B L : ℕ) :
    blockPrefix (wordBlock w L) B = splitWord B L ∘ wordAt w (B * L) := by
  funext t i j
  change w (t + i.val * L + j.val) = w (t + (j.val + L * i.val))
  congr 1
  ac_rfl

theorem condEntropy_wordBlocks {K U : Type*}
    [Fintype K] [MeasurableSpace K] [MeasurableSingletonClass K]
    [MeasurableSpace U] (μ : Measure ℕ) (w : ℕ → K) (Z : ℕ → U) (B L : ℕ) :
    condEntropy (blockPrefix (wordBlock w L) B) Z μ =
      condEntropy (wordAt w (B * L)) Z μ := by
  rw [blockPrefix_wordBlock_eq_split]
  exact condEntropy_comp_of_injective μ (measurable_of_countable _) (splitWord B L)
    (splitWord_injective B L)

/-- A residue process determined by the letters has an exact prefix-sum law. -/
theorem residue_shift_word_sum {K G : Type*} [AddCommMonoid G]
    (w : ℕ → K) (contribution : K → G) (Z : ℕ → G)
    (hstep : ∀ t, Z (t + 1) = Z t + contribution (w t)) (t n : ℕ) :
    Z (t + n) = Z t + ∑ i : Fin n, contribution (wordAt w n t i) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [← Nat.add_assoc, hstep, ih, Fin.sum_univ_castSucc]
    simp only [wordAt, Fin.val_castSucc, Fin.val_last]
    rw [add_assoc]

def blockResidueRecover {K G : Type*} [AddCommMonoid G]
    (contribution : K → G) (L i : ℕ) (data : (Fin i → Fin L → K) × G) : G :=
  data.2 + ∑ b : Fin i, ∑ j : Fin L, contribution (data.1 b j)

theorem wordBlock_residue_reconstruct {K G : Type*} [AddCommMonoid G]
    (w : ℕ → K) (contribution : K → G) (Z : ℕ → G)
    (hstep : ∀ t, Z (t + 1) = Z t + contribution (w t)) (L i t : ℕ) :
    Z (t + i * L) =
      blockResidueRecover contribution L i (blockPrefix (wordBlock w L) i t, Z t) := by
  induction i with
  | zero => simp [blockResidueRecover]
  | succ i ih =>
    rw [Nat.succ_mul, ← Nat.add_assoc,
      residue_shift_word_sum w contribution Z hstep (t + i * L) L, ih]
    simp only [blockResidueRecover, Fin.sum_univ_castSucc, blockPrefix, wordBlock,
      Fin.val_castSucc, Fin.val_last]
    rw [add_assoc]

/-- The long-word bound conditions each block only on its shifted start
residue, using the proved additive reconstruction, rather than dropping
the prefix without justification. -/
theorem condEntropy_word_le_shifted_blocks {K G : Type*}
    [Fintype K] [MeasurableSpace K] [MeasurableSingletonClass K]
    [Fintype G] [AddCommMonoid G] [MeasurableSpace G] [MeasurableSingletonClass G]
    (μ : Measure ℕ) [IsProbabilityMeasure μ]
    (w : ℕ → K) (contribution : K → G) (Z : ℕ → G)
    (hstep : ∀ t, Z (t + 1) = Z t + contribution (w t)) (B L : ℕ) :
    condEntropy (wordAt w (B * L)) Z μ ≤
      ∑ i ∈ Finset.range B,
        condEntropy (fun t => wordAt w L (t + i * L))
          (fun t => Z (t + i * L)) μ := by
  rw [← condEntropy_wordBlocks μ w Z B L]
  exact condEntropy_blockPrefix_le_reconstructed μ (wordBlock w L)
    (fun _ => measurable_of_countable _) Z (measurable_of_countable _)
    (fun i t => Z (t + i * L)) (blockResidueRecover contribution L) B
    (fun i _ t => wordBlock_residue_reconstruct w contribution Z hstep L i t)

/-- Normalized comparison under one actual smoothed law. All shifts and
word lengths are explicit; no stationarity is postulated. -/
theorem smoothedTimeLaw_word_block_rate {Ω K G : Type*}
    [Fintype Ω] [MeasurableSpace Ω] [MeasurableSingletonClass Ω]
    [Fintype K] [MeasurableSpace K] [MeasurableSingletonClass K]
    [Fintype G] [AddCommMonoid G] [MeasurableSpace G] [MeasurableSingletonClass G]
    [MeasurableSpace Bool] [MeasurableSingletonClass Bool]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (b : Ω → ℕ) (N : ℕ) [NeZero N]
    (w : ℕ → K) (contribution : K → G) (Z : ℕ → G)
    (hstep : ∀ t, Z (t + 1) = Z t + contribution (w t))
    (B L : ℕ) (hB : 0 < B) (hL : 0 < L) (T : ℝ)
    (hT : 1 ≤ T) (hBL : ((B * L : ℕ) : ℝ) ≤ T) (hN : T ^ 10 ≤ (N : ℝ)) :
    condEntropy (wordAt w (B * L)) Z (smoothedTimeLaw μ b N) / (B * L : ℕ) ≤
      condEntropy (wordAt w L) Z (smoothedTimeLaw μ b N) / L +
        ((1 + 9 * Real.log T + L * Real.log (Fintype.card K)) / T ^ 9) / L := by
  let ν := smoothedTimeLaw μ b N
  let E := (1 + 9 * Real.log T + L * Real.log (Fintype.card K)) / T ^ 9
  have hs := condEntropy_word_le_shifted_blocks ν w contribution Z hstep B L
  have hi : ∀ i ∈ Finset.range B,
      condEntropy (fun t => wordAt w L (t + i * L)) (fun t => Z (t + i * L)) ν ≤
        condEntropy (wordAt w L) Z ν + E := by
    intro i hi
    have hshift : ((i * L : ℕ) : ℝ) ≤ T := by
      exact (Nat.cast_le.mpr (Nat.mul_le_mul_right L (Finset.mem_range.mp hi).le)).trans hBL
    have hc := smoothedTimeLaw_word_condEntropy_source_bound μ b N L (wordAt w L) Z
      (i * L) T hT hshift hN
    have hh := (abs_le.mp hc).2
    change _ - condEntropy (wordAt w L) Z ν ≤ E at hh
    linarith
  have hsum := hs.trans (Finset.sum_le_sum hi)
  have hsum' : condEntropy (wordAt w (B * L)) Z ν ≤
      B * (condEntropy (wordAt w L) Z ν + E) := by
    simpa only [Finset.sum_const, Finset.card_range, nsmul_eq_mul] using hsum
  have hBr : (0 : ℝ) < B := Nat.cast_pos.mpr hB
  have hLr : (0 : ℝ) < L := Nat.cast_pos.mpr hL
  have hd := div_le_div_of_nonneg_right hsum' (mul_nonneg hBr.le hLr.le)
  rw [Nat.cast_mul] at ⊢
  convert hd using 1
  dsimp [ν, E]
  field_simp

end BinaryFormMoat.EntropyIntegration

#print axioms BinaryFormMoat.EntropyIntegration.splitWord_injective
#print axioms BinaryFormMoat.EntropyIntegration.blockPrefix_wordBlock_eq_split
#print axioms BinaryFormMoat.EntropyIntegration.condEntropy_wordBlocks
#print axioms BinaryFormMoat.EntropyIntegration.residue_shift_word_sum
#print axioms BinaryFormMoat.EntropyIntegration.wordBlock_residue_reconstruct
#print axioms BinaryFormMoat.EntropyIntegration.condEntropy_word_le_shifted_blocks
#print axioms BinaryFormMoat.EntropyIntegration.smoothedTimeLaw_word_block_rate
