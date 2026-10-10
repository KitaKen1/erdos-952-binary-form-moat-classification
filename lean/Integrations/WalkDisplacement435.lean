import Moat.LinearFactors
import Integrations.PosteriorEntropy435
import Mathlib.Data.Int.Interval

namespace BinaryFormMoat.EntropyIntegration
open MeasureTheory ProbabilityTheory

/-- An exact finite alphabet for a physical lattice displacement. -/
def displacementBox (B : ℕ) : Finset Point :=
  (Finset.Icc (-(B : ℤ)) B) ×ˢ (Finset.Icc (-(B : ℤ)) B)

abbrev BoundedDisplacement (B : ℕ) := ↥(displacementBox B)

theorem mem_displacementBox (B : ℕ) (v : Point) :
    v ∈ displacementBox B ↔ |v.1| ≤ B ∧ |v.2| ≤ B := by
  simp [displacementBox, abs_le]

theorem displacementBox_card (B : ℕ) : (displacementBox B).card = (2 * B + 1) ^ 2 := by
  have h : (Finset.Icc (-(B : ℤ)) B).card = 2 * B + 1 := by
    rw [Int.card_Icc]
    omega
  simp [displacementBox, h, pow_two]

theorem boundedDisplacement_card (B : ℕ) :
    Fintype.card (BoundedDisplacement B) = (2 * B + 1) ^ 2 := by
  exact (Fintype.card_coe _).trans (displacementBox_card B)

def zeroDisplacement (B : ℕ) : BoundedDisplacement B :=
  ⟨0, (mem_displacementBox B 0).mpr (by simp)⟩

/-- Coordinate increments telescope without a square-root or path-length API. -/
theorem coordinate_displacement_le (w : ℕ → ℤ) (D : ℕ)
    (hstep : ∀ t, |w (t + 1) - w t| ≤ D) (t n : ℕ) :
    |w (t + n) - w t| ≤ (D * n : ℕ) := by
  induction n with
  | zero => simp
  | succ n ih =>
    have ht := abs_sub_le (w (t + n + 1)) (w (t + n)) (w t)
    have hs := hstep (t + n)
    have he : (D * (n + 1) : ℕ) = D * n + D := by simp [Nat.mul_add]
    rw [he, Nat.cast_add]
    simpa only [Nat.add_assoc, add_comm] using ht.trans (add_le_add hs ih)

theorem walk_displacement_mem (z : ℕ → Point) (D : ℕ)
    (hstep : ∀ t, |(z (t + 1)).1 - (z t).1| ≤ D ∧
      |(z (t + 1)).2 - (z t).2| ≤ D)
    (S t u : ℕ) (htu : t ≤ u) (hu : u ≤ t + S) :
    z u - z t ∈ displacementBox (D * S) := by
  apply (mem_displacementBox _ _).mpr
  have hn : u - t ≤ S := by omega
  have hm : ((D * (u - t) : ℕ) : ℤ) ≤ D * S := by
    exact_mod_cast Nat.mul_le_mul_left D hn
  have hx := coordinate_displacement_le (fun v => (z v).1) D (fun v => (hstep v).1) t (u - t)
  have hy := coordinate_displacement_le (fun v => (z v).2) D (fun v => (hstep v).2) t (u - t)
  have he : t + (u - t) = u := by omega
  rw [he] at hx hy
  exact ⟨hx.trans hm, hy.trans hm⟩

/-- The graph's squared-step convention supplies a uniform integral bound. -/
theorem sqDist_walk_coordinate_steps (z : ℕ → Point) (R : ℕ)
    (hstep : ∀ t, sqDist (z (t + 1)) (z t) ≤ (R : ℤ)) :
    ∀ t, |(z (t + 1)).1 - (z t).1| ≤ (R + 1 : ℕ) ∧
      |(z (t + 1)).2 - (z t).2| ≤ (R + 1 : ℕ) := by
  intro t
  constructor
  · simpa using linear_step_bound 1 0 R (z (t + 1)) (z t) (hstep t)
  · simpa using linear_step_bound 0 1 R (z (t + 1)) (z t) (hstep t)

/-- Trial data pays logarithmic displacement radius, rather than the full
walk-word length. This holds for any law on the bounded alphabet. -/
theorem boundedDisplacement_data_entropy_le {A J : Type*}
    [MeasurableSpace A] [Fintype J] (B : ℕ)
    (μ : Measure (A × (J → BoundedDisplacement B))) :
    entropy (Prod.snd : A × (J → BoundedDisplacement B) → J → BoundedDisplacement B) μ ≤
      (Fintype.card J : ℝ) * (2 * Real.log (2 * B + 1 : ℕ)) := by
  classical
  have h := entropy_le_log_card
    (Prod.snd : A × (J → BoundedDisplacement B) → J → BoundedDisplacement B) μ
  simpa only [Fintype.card_fun, boundedDisplacement_card, Nat.cast_pow, Real.log_pow,
    Nat.cast_ofNat] using h

/-- Explicit source-form O_D(1): separate maximum shift from the fixed
coordinate-step constant, without asymptotics or a disk counting theorem. -/
theorem displacement_log_bound (D S : ℕ) :
    2 * Real.log (2 * (D * S) + 1 : ℕ) ≤
      2 * Real.log (S + 1 : ℕ) + 2 * Real.log (2 * D + 1 : ℕ) := by
  have hn : 2 * (D * S) + 1 ≤ (2 * D + 1) * (S + 1) := by nlinarith
  have hr : ((2 * (D * S) + 1 : ℕ) : ℝ) ≤ ((2 * D + 1) * (S + 1) : ℕ) := by
    exact_mod_cast hn
  have h := Real.log_le_log (by positivity : (0 : ℝ) < (2 * (D * S) + 1 : ℕ))
    hr
  rw [Nat.cast_mul, Real.log_mul (by positivity) (by positivity)] at h
  linarith

end BinaryFormMoat.EntropyIntegration

#print axioms BinaryFormMoat.EntropyIntegration.mem_displacementBox
#print axioms BinaryFormMoat.EntropyIntegration.displacementBox_card
#print axioms BinaryFormMoat.EntropyIntegration.boundedDisplacement_card
#print axioms BinaryFormMoat.EntropyIntegration.coordinate_displacement_le
#print axioms BinaryFormMoat.EntropyIntegration.walk_displacement_mem
#print axioms BinaryFormMoat.EntropyIntegration.sqDist_walk_coordinate_steps
#print axioms BinaryFormMoat.EntropyIntegration.boundedDisplacement_data_entropy_le
#print axioms BinaryFormMoat.EntropyIntegration.displacement_log_bound
