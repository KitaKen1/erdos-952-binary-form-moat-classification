import Integrations.InformationRate435
import Integrations.RootResidues435

namespace BinaryFormMoat.EntropyIntegration
open MeasureTheory ProbabilityTheory

/-- The actual increments of a lattice walk, in a finite alphabet supplied
by the graph's squared-step bound. No encoding hypothesis is postulated. -/
def walkLetters (z : ℕ → Point) (R : ℕ)
    (hstep : ∀ t, sqDist (z (t + 1)) (z t) ≤ (R : ℤ)) :
    ℕ → BoundedDisplacement (R + 1) :=
  fun t => ⟨z (t + 1) - z t, (mem_displacementBox _ _).mpr
    (sqDist_walk_coordinate_steps z R hstep t)⟩

theorem walkLetters_val (z : ℕ → Point) (R : ℕ)
    (hstep : ∀ t, sqDist (z (t + 1)) (z t) ≤ (R : ℤ)) (t : ℕ) :
    (walkLetters z R hstep t).val = z (t + 1) - z t := rfl

theorem walkLetters_residue_step {G : Type*} [AddCommGroup G]
    (z : ℕ → Point) (R : ℕ)
    (hstep : ∀ t, sqDist (z (t + 1)) (z t) ≤ (R : ℤ))
    (φ : Point →+ G) (t : ℕ) :
    φ (z (t + 1)) = φ (z t) + φ (walkLetters z R hstep t).val := by
  rw [walkLetters_val, map_sub]
  simp

theorem walkLetters_log_card (R : ℕ) :
    Real.log (Fintype.card (BoundedDisplacement (R + 1))) =
      2 * Real.log (2 * (R + 1) + 1 : ℕ) := by
  rw [boundedDisplacement_card, Nat.cast_pow, Real.log_pow]
  norm_num

/-- Normalized common-law information budget for the actual finite words
and additive residue observations of any bounded-step lattice walk.
The observation group may be a finite product of prime residue fields. -/
theorem smoothedTimeLaw_walk_word_budget {Ω G : Type*}
    [Fintype Ω] [MeasurableSpace Ω] [MeasurableSingletonClass Ω]
    [Fintype G] [AddCommGroup G] [MeasurableSpace G] [MeasurableSingletonClass G]
    [MeasurableSpace Bool] [MeasurableSingletonClass Bool]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (b : Ω → ℕ) (N : ℕ) [NeZero N]
    (z : ℕ → Point) (R : ℕ)
    (hstep : ∀ t, sqDist (z (t + 1)) (z t) ≤ (R : ℤ))
    (φ : ℕ → Point →+ G) (L B : ℕ → ℕ) (hL : ∀ i, 0 < L i) (n : ℕ)
    (hB : ∀ i < n, 0 < B i) (hblock : ∀ i < n, L (i + 1) = B i * L i)
    (T : ℝ) (hT : 1 ≤ T) (hlong : ∀ i < n, (L (i + 1) : ℝ) ≤ T)
    (hN : T ^ 10 ≤ (N : ℝ)) :
    (∑ i ∈ Finset.range (n + 1),
      condMutualInfo (fun t => φ i (z t)) (wordAt (walkLetters z R hstep) (L i))
        (observationHistory (fun j t => φ j (z t)) i) (smoothedTimeLaw μ b N) / L i) ≤
      2 * Real.log (2 * (R + 1) + 1 : ℕ) +
        n * ((1 + 9 * Real.log T + 2 * Real.log (2 * (R + 1) + 1 : ℕ)) / T ^ 9) := by
  have h := smoothedTimeLaw_varying_word_uniform_budget μ b N (walkLetters z R hstep)
    (fun i v => φ i v.val) (fun i t => φ i (z t))
    (fun i t => walkLetters_residue_step z R hstep (φ i) t)
    L B hL n hB hblock T hT hlong hN
  simpa only [walkLetters_log_card] using h

/-- The ceiling-length version constructs the offset scale required by
the budget, so it has no assumed terminal-window length. -/
theorem smoothedTimeLaw_walk_word_ceiling_budget {Ω G : Type*}
    [Fintype Ω] [MeasurableSpace Ω] [MeasurableSingletonClass Ω]
    [Fintype G] [AddCommGroup G] [MeasurableSpace G] [MeasurableSingletonClass G]
    [MeasurableSpace Bool] [MeasurableSingletonClass Bool]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (b : Ω → ℕ)
    (z : ℕ → Point) (R : ℕ)
    (hstep : ∀ t, sqDist (z (t + 1)) (z t) ≤ (R : ℤ))
    (φ : ℕ → Point →+ G) (L B : ℕ → ℕ) (hL : ∀ i, 0 < L i) (n : ℕ)
    (hB : ∀ i < n, 0 < B i) (hblock : ∀ i < n, L (i + 1) = B i * L i)
    (T : ℝ) (hT : 1 ≤ T) (hlong : ∀ i < n, (L (i + 1) : ℝ) ≤ T) :
    (∑ i ∈ Finset.range (n + 1),
      condMutualInfo (fun t => φ i (z t)) (wordAt (walkLetters z R hstep) (L i))
        (observationHistory (fun j t => φ j (z t)) i)
        (smoothedTimeLaw μ b (terminalSmoothingLength T)) / L i) ≤
      2 * Real.log (2 * (R + 1) + 1 : ℕ) +
        n * ((1 + 9 * Real.log T + 2 * Real.log (2 * (R + 1) + 1 : ℕ)) / T ^ 9) := by
  have : NeZero (terminalSmoothingLength T) := ⟨(terminalSmoothingLength_pos T).ne'⟩
  exact smoothedTimeLaw_walk_word_budget μ b (terminalSmoothingLength T) z R hstep
    φ L B hL n hB hblock T hT hlong (terminalSmoothingLength_ge T)

theorem dyadic_block_length (level : ℕ → ℕ) (hlevel : Monotone level) (i : ℕ) :
    2 ^ level (i + 1) = 2 ^ (level (i + 1) - level i) * 2 ^ level i := by
  rw [← pow_add, Nat.sub_add_cancel (hlevel (Nat.le_succ i))]

theorem dyadic_length_le_last (level : ℕ → ℕ) (hlevel : Monotone level)
    (i n : ℕ) (hi : i ≤ n) :
    (2 : ℕ) ^ level i ≤ 2 ^ level n := by
  exact Nat.pow_le_pow_right (by omega) (hlevel hi)

/-- Fully constructed dyadic block factors and terminal smoothing length.
The last dyadic length bounds all earlier shifts; the walk and source law
are otherwise arbitrary. Actual information lower bounds remain a separate
geometric obligation. -/
theorem smoothedTimeLaw_walk_dyadic_budget {Ω G : Type*}
    [Fintype Ω] [MeasurableSpace Ω] [MeasurableSingletonClass Ω]
    [Fintype G] [AddCommGroup G] [MeasurableSpace G] [MeasurableSingletonClass G]
    [MeasurableSpace Bool] [MeasurableSingletonClass Bool]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (b : Ω → ℕ)
    (z : ℕ → Point) (R : ℕ)
    (hstep : ∀ t, sqDist (z (t + 1)) (z t) ≤ (R : ℤ))
    (φ : ℕ → Point →+ G) (level : ℕ → ℕ) (hlevel : Monotone level) (n : ℕ)
    (T : ℝ) (hT : 1 ≤ T) (hlast : ((2 ^ level n : ℕ) : ℝ) ≤ T) :
    (∑ i ∈ Finset.range (n + 1),
      condMutualInfo (fun t => φ i (z t)) (wordAt (walkLetters z R hstep) (2 ^ level i))
        (observationHistory (fun j t => φ j (z t)) i)
        (smoothedTimeLaw μ b (terminalSmoothingLength T)) / (2 ^ level i : ℕ)) ≤
      2 * Real.log (2 * (R + 1) + 1 : ℕ) +
        n * ((1 + 9 * Real.log T + 2 * Real.log (2 * (R + 1) + 1 : ℕ)) / T ^ 9) := by
  apply smoothedTimeLaw_walk_word_ceiling_budget μ b z R hstep φ
    (fun i => 2 ^ level i) (fun i => 2 ^ (level (i + 1) - level i))
    (fun _ => pow_pos (by omega) _) n (fun _ _ => pow_pos (by omega) _)
    (fun i _ => dyadic_block_length level hlevel i) T hT
  intro i hi
  exact (Nat.cast_le.mpr (dyadic_length_le_last level hlevel (i + 1) n
    (by omega))).trans hlast

end BinaryFormMoat.EntropyIntegration

#print axioms BinaryFormMoat.EntropyIntegration.walkLetters_val
#print axioms BinaryFormMoat.EntropyIntegration.walkLetters_residue_step
#print axioms BinaryFormMoat.EntropyIntegration.walkLetters_log_card
#print axioms BinaryFormMoat.EntropyIntegration.smoothedTimeLaw_walk_word_budget
#print axioms BinaryFormMoat.EntropyIntegration.smoothedTimeLaw_walk_word_ceiling_budget
#print axioms BinaryFormMoat.EntropyIntegration.dyadic_block_length
#print axioms BinaryFormMoat.EntropyIntegration.dyadic_length_le_last
#print axioms BinaryFormMoat.EntropyIntegration.smoothedTimeLaw_walk_dyadic_budget
