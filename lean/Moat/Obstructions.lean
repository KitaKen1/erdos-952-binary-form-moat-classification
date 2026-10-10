import Moat.Basic
import Mathlib.Tactic.Linarith

namespace BinaryFormMoat

/-- An injective bounded-step walk contradicts a uniform component-size bound. -/
theorem not_uniformMoat_of_walk (F : Form) (r R : ℕ) (z : ℕ → Point)
    (hz : Function.Injective z) (ha : ∀ n, Allowed F r (z n))
    (hs : ∀ n, sqDist (z n) (z (n + 1)) ≤ (R : ℤ)) : ¬ UniformMoat F := by
  intro h
  obtain ⟨B, hB⟩ := h R r
  let v : ℕ → {z : Point // Allowed F r z} := fun n => ⟨z n, ha n⟩
  have hv : Function.Injective v := by
    intro n m hnm
    exact hz (congrArg Subtype.val hnm)
  have reach (n : ℕ) : (graph F r R).Reachable (v 0) (v n) := by
    induction n with
    | zero => exact SimpleGraph.Reachable.refl _
    | succ n ih =>
      apply ih.trans
      apply SimpleGraph.Adj.reachable
      exact ⟨fun he => Nat.ne_of_lt (Nat.lt_succ_self n) (hv he), hs n⟩
  have hfinite := Set.finite_of_encard_le_coe (hB (v 0))
  have hrange : Set.range v ⊆ {w | (graph F r R).Reachable (v 0) w} := by
    rintro _ ⟨n, rfl⟩
    exact reach n
  exact (Set.infinite_range_of_injective hv) (hfinite.subset hrange)

/-- A constant-value fibre of a linear form, parametrized by natural numbers. -/
def fibrePoint (a b : ℤ) (n : ℕ) : Point :=
  (a + b * (n : ℤ), b - a * (n : ℤ))

theorem fibrePoint_injective (a b : ℤ) (hab : a ≠ 0 ∨ b ≠ 0) :
    Function.Injective (fibrePoint a b) := by
  intro n m h
  have h₁ := congrArg Prod.fst h
  have h₂ := congrArg Prod.snd h
  change a + b * (n : ℤ) = a + b * (m : ℤ) at h₁
  change b - a * (n : ℤ) = b - a * (m : ℤ) at h₂
  rcases hab with ha | hb
  · have he : (n : ℤ) = (m : ℤ) := mul_left_cancel₀ ha (by linarith [h₂])
    exact_mod_cast he
  · have he : (n : ℤ) = (m : ℤ) := mul_left_cancel₀ hb (by linarith [h₁])
    exact_mod_cast he

theorem fibrePoint_step (a b : ℤ) (n : ℕ) :
    sqDist (fibrePoint a b n) (fibrePoint a b (n + 1)) = a^2 + b^2 := by
  simp only [sqDist, fibrePoint, Nat.cast_add, Nat.cast_one]
  ring

/-- Every exceptional form has an infinite bounded-step walk at a fixed budget. -/
theorem not_uniformMoat_of_isLinearPower (F : Form) (h : IsLinearPower F) :
    ¬ UniformMoat F := by
  obtain ⟨c, a, b, m, hc, hab, hm, rfl⟩ := h
  have hq : a^2 + b^2 ≠ 0 := by
    rcases hab with ha | hb
    · nlinarith [sq_pos_of_ne_zero ha, sq_nonneg b]
    · nlinarith [sq_pos_of_ne_zero hb, sq_nonneg a]
  let q : ℤ := c * (a^2 + b^2)^m
  have hq0 : q ≠ 0 := mul_ne_zero hc (pow_ne_zero _ hq)
  have heval (n : ℕ) :
      value (MvPolynomial.C c * (MvPolynomial.C a * MvPolynomial.X (0 : Fin 2) +
        MvPolynomial.C b * MvPolynomial.X (1 : Fin 2))^m) (fibrePoint a b n) = q := by
    simp only [value, fibrePoint, MvPolynomial.eval_mul, MvPolynomial.eval_C,
      MvPolynomial.eval_pow, MvPolynomial.eval_add, MvPolynomial.eval_X,
      Matrix.cons_val_zero, Matrix.cons_val_one]
    congr 2
    ring
  apply not_uniformMoat_of_walk _ (omega q) (a^2 + b^2).natAbs (fibrePoint a b)
    (fibrePoint_injective a b hab)
  · intro n
    change value _ _ ≠ 0 ∧ omega (value _ _) ≤ omega q
    rw [heval]
    exact ⟨hq0, le_rfl⟩
  · intro n
    rw [fibrePoint_step]
    exact Int.le_natAbs

/-- The necessity direction of the classification is unconditional. -/
theorem not_isLinearPower_of_uniformMoat (F : Form) (h : UniformMoat F) :
    ¬ IsLinearPower F := fun he => not_uniformMoat_of_isLinearPower F he h

end BinaryFormMoat
