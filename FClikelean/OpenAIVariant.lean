module

public import FormalConjecturesUtil

/-! # Uniform Gaussian moat variant -/

@[expose] public section

namespace Erdos952

/-- OpenAI's uniform Gaussian moat theorem. -/
@[category research solved, AMS 5 11]
theorem erdos_952_openai : answer(False) ↔
  ∃ C : ℤ, ∀ N : ℕ, ∃ x : ℕ → GaussianInt,
    Function.Injective x ∧
      ∀ n ≤ N, Prime (x n) ∧ (n < N → (x (n + 1) - x n).norm < C) := by
  sorry

end Erdos952
