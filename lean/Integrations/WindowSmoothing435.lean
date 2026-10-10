import Mathlib.Probability.UniformOn
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Integral.Bochner.SumMeasure
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

namespace BinaryFormMoat.EntropyIntegration
open MeasureTheory ProbabilityTheory

/-- The uniform average on a consecutive window of length `N`. -/
noncomputable def windowAverage (f : ℕ → ℝ) (b N : ℕ) : ℝ :=
  (∑ i ∈ Finset.range N, f (b + i)) / N

/-- Sliding a window cancels its interior; only the two boundary sums remain.
The identity also holds when the shift exceeds the window length. -/
theorem window_sum_shift_identity (f : ℕ → ℝ) (b N a : ℕ) :
    (∑ i ∈ Finset.range N, f (b + i + a)) -
      (∑ i ∈ Finset.range N, f (b + i)) =
    (∑ i ∈ Finset.range a, f (b + N + i)) -
      (∑ i ∈ Finset.range a, f (b + i)) := by
  have h₁ := Finset.sum_range_add (fun i => f (b + i)) N a
  have h₂ := Finset.sum_range_add (fun i => f (b + i)) a N
  have h₃ : (∑ i ∈ Finset.range N, f (b + (a + i))) =
      ∑ i ∈ Finset.range N, f (b + i + a) := by
    apply Finset.sum_congr rfl
    intro i _
    congr 1
    omega
  rw [h₃, Nat.add_comm a N] at h₂
  simp only [Nat.add_assoc] at *
  linarith

theorem window_sum_nonneg (f : ℕ → ℝ) (hf : ∀ i, 0 ≤ f i) (b N : ℕ) :
    0 ≤ ∑ i ∈ Finset.range N, f (b + i) :=
  Finset.sum_nonneg (fun i _ => hf (b + i))

theorem window_sum_le_length (f : ℕ → ℝ) (hf : ∀ i, f i ≤ 1) (b N : ℕ) :
    (∑ i ∈ Finset.range N, f (b + i)) ≤ N := by
  calc
    _ ≤ ∑ _i ∈ Finset.range N, (1 : ℝ) := Finset.sum_le_sum (fun i _ => hf (b + i))
    _ = N := by simp

/-- A `[0,1]` test function changes by at most `a/N` under a time shift. -/
theorem windowAverage_shift_bound (f : ℕ → ℝ)
    (h₀ : ∀ i, 0 ≤ f i) (h₁ : ∀ i, f i ≤ 1) (b N a : ℕ) (hN : 0 < N) :
    |windowAverage f (b + a) N - windowAverage f b N| ≤ (a : ℝ) / N := by
  have hb₀ := window_sum_nonneg f h₀ b a
  have hb₁ := window_sum_le_length f h₁ b a
  have he₀ := window_sum_nonneg f h₀ (b + N) a
  have he₁ := window_sum_le_length f h₁ (b + N) a
  have hid := window_sum_shift_identity f b N a
  have hsum : |(∑ i ∈ Finset.range N, f (b + a + i)) -
      (∑ i ∈ Finset.range N, f (b + i))| ≤ (a : ℝ) := by
    have heq : (∑ i ∈ Finset.range N, f (b + a + i)) =
        ∑ i ∈ Finset.range N, f (b + i + a) := by
      apply Finset.sum_congr rfl
      intro i _
      congr 1
      omega
    rw [heq, hid, abs_le]
    constructor <;> linarith
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  simpa only [windowAverage, ← sub_div, abs_div, abs_of_pos hNr] using
    (div_le_div_of_nonneg_right hsum hNr.le)

end BinaryFormMoat.EntropyIntegration

#print axioms BinaryFormMoat.EntropyIntegration.window_sum_shift_identity
#print axioms BinaryFormMoat.EntropyIntegration.window_sum_nonneg
#print axioms BinaryFormMoat.EntropyIntegration.window_sum_le_length
#print axioms BinaryFormMoat.EntropyIntegration.windowAverage_shift_bound
