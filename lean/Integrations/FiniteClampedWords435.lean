import Integrations.CountableFamilyHistory435
import Integrations.WalkWordBudget435

noncomputable section
open scoped Classical
namespace BinaryFormMoat.EntropyIntegration
open MeasureTheory ProbabilityTheory

/-- Extend the ACTUAL finite monotone word levels constantly at the last
batch; empty families receive level zero. No extra observation is revealed. -/
def finiteClampedLevel {N : ℕ} (l : Fin N → ℕ) (n : ℕ) : ℕ :=
  if h : 0 < N then l ⟨min n (N - 1), by omega⟩ else 0

theorem finiteClampedLevel_get {N : ℕ} (l : Fin N → ℕ) (k : Fin N) :
    finiteClampedLevel l k.val = l k := by
  have hN : 0 < N := by have := k.isLt; omega
  simp only [finiteClampedLevel, dite_eq_left hN]
  congr 1
  apply Fin.ext
  exact min_eq_left (by omega)

theorem finiteClampedLevel_mono {N : ℕ} (l : Fin N → ℕ) (hl : Monotone l) :
    Monotone (finiteClampedLevel l) := by
  intro n m hnm
  by_cases hN : 0 < N
  · simp only [finiteClampedLevel, dite_eq_left hN]
    exact hl (min_le_min_right (N - 1) hnm)
  · simp only [finiteClampedLevel, dite_eq_right hN, le_refl]

theorem finiteClampedLevel_word_bound {N : ℕ} (l : Fin N → ℕ) (T : ℝ)
    (hT : 1 ≤ T) (h : ∀ k, ((2 ^ l k : ℕ) : ℝ) ≤ T) (n : ℕ) :
    ((2 ^ finiteClampedLevel l n : ℕ) : ℝ) ≤ T := by
  by_cases hN : 0 < N
  · simp only [finiteClampedLevel, dite_eq_left hN]
    exact h _
  · simpa only [finiteClampedLevel, dite_eq_right hN, pow_zero, Nat.cast_one] using hT

/-- A faithful common-group observation sequence has exactly zero
conditional information after the actual finite family. -/
theorem finiteFamilyBatch_information_dummy {N : ℕ}
    (K : Fin N → Type*) [∀ i, AddCommGroup (K i)] [∀ i, Fintype (K i)]
    [∀ i, MeasurableSpace (K i)] [∀ i, MeasurableSingletonClass (K i)]
    (Φ : ∀ i, Point →+ K i) (μ : Measure ℕ) [IsProbabilityMeasure μ]
    (z : ℕ → Point) {T U : Type*} [Fintype T] [MeasurableSpace T] [MeasurableSingletonClass T]
    [Fintype U] [MeasurableSpace U] [MeasurableSingletonClass U]
    (W : ℕ → T) (O : ℕ → U) (n : ℕ) (hn : N ≤ n) :
    condMutualInfo (fun v => finiteFamilyBatchHom K Φ n (z v)) W O μ = 0 := by
  simp only [finiteFamilyBatchHom, dite_eq_right (not_lt_of_ge hn), AddMonoidHom.zero_apply]
  let X := fun _ : ℕ => (0 : (i : Fin N) → K i)
  have hc : condEntropy X O μ = 0 := by
    have h := condEntropy_le_entropy μ (measurable_of_countable X) (measurable_of_countable O)
    simp only [X, entropy_const] at h
    exact le_antisymm h (condEntropy_nonneg X O μ)
  have hc' : condEntropy X (fun v => (W v, O v)) μ = 0 := by
    have h := condEntropy_le_entropy μ (measurable_of_countable X)
      (measurable_of_countable (fun v => (W v, O v)))
    simp only [X, entropy_const] at h
    exact le_antisymm h (condEntropy_nonneg X _ μ)
  change condMutualInfo X W O μ = 0
  rw [condMutualInfo_eq' (measurable_of_countable X) (measurable_of_countable W)
    (measurable_of_countable O) μ, hc, hc', sub_self]

end BinaryFormMoat.EntropyIntegration
#print axioms BinaryFormMoat.EntropyIntegration.finiteClampedLevel
#print axioms BinaryFormMoat.EntropyIntegration.finiteClampedLevel_get
#print axioms BinaryFormMoat.EntropyIntegration.finiteClampedLevel_mono
#print axioms BinaryFormMoat.EntropyIntegration.finiteClampedLevel_word_bound
#print axioms BinaryFormMoat.EntropyIntegration.finiteFamilyBatch_information_dummy
