module

public import FormalConjecturesUtil

/-! # Uniform Gaussian moat variant -/

@[expose] public section

namespace Erdos952

/-- OpenAI's uniform Gaussian moat theorem. -/
@[category research solved, AMS 5 11,
  formal_proof using lean4 at "https://github.com/KitaKen1/erdos-952-binary-form-moat-classification/blob/b0b614662c342e2610fdfe6897691f9b54d33afb/lean/OpenAIVariant.lean#L55"]
theorem erdos_952_openai : answer(False) ↔
  ∃ C : ℤ, ∀ N : ℕ, ∃ x : ℕ → GaussianInt,
    Function.Injective x ∧
      ∀ n ≤ N, Prime (x n) ∧ (n < N → (x (n + 1) - x n).norm < C) := by
  sorry

end Erdos952
