import Integrations.PaperGeometricFamily435

noncomputable section
open scoped Classical
namespace BinaryFormMoat.GeometryIntegration
open EntropyIntegration MeasureTheory ProbabilityTheory

/-- A selected residue tuple pays at most the full batch's p-letter alphabet,
for every choice of root labels and every actual probability law. -/
theorem selected_prime_batch_entropy_le {Ω : Type*} [Fintype Ω] [MeasurableSpace Ω]
    [MeasurableSingletonClass Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (P S : Finset ℕ) [∀ p : S, NeZero p.val] (hS : S ⊆ P)
    (U : ℕ) (hU : 1 ≤ U) (hP : ∀ p ∈ P, p ≤ U)
    (X : (p : S) → Ω → ZMod p.val) :
    entropy (fun ω p => X p ω) μ ≤ (P.card : ℝ) * Real.log U := by
  have h := entropy_le_log_card (fun ω p => X p ω) μ
  rw [Fintype.card_pi, Nat.cast_prod,
    Real.log_prod (fun p _ => by exact_mod_cast (Fintype.card_ne_zero :
      Fintype.card (ZMod p.val) ≠ 0))] at h
  simp only [ZMod.card] at h
  have hs : (∑ p : S, Real.log (p.val : ℝ)) ≤ (S.card : ℝ) * Real.log U := by
    calc
      _ ≤ ∑ _p : S, Real.log (U : ℝ) := Finset.sum_le_sum fun p _ =>
        Real.log_le_log (by exact_mod_cast (NeZero.pos p.val))
          (by exact_mod_cast hP p.val (hS p.property))
      _ = _ := by simp
  have hcard : (S.card : ℝ) ≤ P.card := by exact_mod_cast Finset.card_le_card hS
  exact h.trans (hs.trans (mul_le_mul_of_nonneg_right hcard
    (Real.log_nonneg (by exact_mod_cast hU))))

/-- ALL smaller selected tuples under ONE actual law. No independence is
assumed between residue coordinates or between batches. -/
theorem smaller_residue_family_entropy_le {Ω : Type*} [Fintype Ω] [MeasurableSpace Ω]
    [MeasurableSingletonClass Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (I : Finset ℕ) (P S : ℕ → Finset ℕ) [∀ i, ∀ p : S i, NeZero p.val]
    (hS : ∀ i ∈ I, S i ⊆ P i) (B : ℕ) (hB : 3 ≤ B)
    (hP : ∀ i ∈ I, ∀ p ∈ P i, p ≤ 2 * B ^ i)
    (X : (i : ℕ) → (p : S i) → Ω → ZMod p.val) (j : ℕ) :
    entropy (fun ω (i : I.filter (fun i => i < j)) p => X i.val p ω) μ ≤
      ∑ i ∈ I.filter (fun i => i < j), ((P i).card : ℝ) * Real.log (2 * B ^ i : ℕ) := by
  let J := I.filter (fun i => i < j)
  have h := entropy_pi_le_sum μ (fun i : J => (p : S i.val) → ZMod p.val)
    (fun i ω p => X i.val p ω) (fun _ => measurable_of_finite _)
  have hs : (∑ i : J, entropy (fun ω p => X i.val p ω) μ) ≤
      ∑ i : J, ((P i.val).card : ℝ) * Real.log (2 * B ^ i.val : ℕ) := by
    apply Finset.sum_le_sum
    intro i _
    have hi : i.val ∈ I := (Finset.mem_filter.mp i.property).1
    exact selected_prime_batch_entropy_le μ (P i.val) (S i.val) (hS i.val hi)
      (2 * B ^ i.val) (by have := pow_pos (by omega : 0 < B) i.val; omega)
      (hP i.val hi) (X i.val)
  exact (h.trans hs).trans_eq (Finset.sum_coe_sort J
    (fun i => ((P i).card : ℝ) * Real.log (2 * B ^ i : ℕ)))

/-- The paper's initial conditional entropy estimate, under the same law
and any fixed auxiliary choices. The full-alphabet cost is supplied above. -/
theorem smaller_residue_family_condEntropy_ge {Ω K : Type*} [Fintype Ω]
    [MeasurableSpace Ω] [MeasurableSingletonClass Ω]
    [Fintype K] [MeasurableSpace K] [MeasurableSingletonClass K]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (I : Finset ℕ) (P S : ℕ → Finset ℕ) [∀ i, ∀ p : S i, NeZero p.val]
    (hS : ∀ i ∈ I, S i ⊆ P i) (B : ℕ) (hB : 3 ≤ B)
    (hP : ∀ i ∈ I, ∀ p ∈ P i, p ≤ 2 * B ^ i)
    (Y : (i : ℕ) → (p : S i) → Ω → ZMod p.val) (j : ℕ) (X : Ω → K) :
    entropy X μ -
      (∑ i ∈ I.filter (fun i => i < j), ((P i).card : ℝ) * Real.log (2 * B ^ i : ℕ)) ≤
    condEntropy X (fun ω (i : I.filter (fun i => i < j)) p => Y i.val p ω) μ := by
  have hO := smaller_residue_family_entropy_le μ I P S hS B hB hP Y j
  have h := condEntropy_ge_entropy_sub_observation_entropy μ X
    (fun ω (i : I.filter (fun i => i < j)) p => Y i.val p ω)
    (measurable_of_finite _) (measurable_of_finite _)
  linarith

theorem smaller_residue_family_condEntropy_accuracy {Ω K : Type*} [Fintype Ω]
    [MeasurableSpace Ω] [MeasurableSingletonClass Ω]
    [Fintype K] [MeasurableSpace K] [MeasurableSingletonClass K]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (I : Finset ℕ) (P S : ℕ → Finset ℕ) [∀ i, ∀ p : S i, NeZero p.val]
    (hS : ∀ i ∈ I, S i ⊆ P i) (B : ℕ) (hB : 3 ≤ B)
    (hP : ∀ i ∈ I, ∀ p ∈ P i, p ≤ 2 * B ^ i)
    (Y : (i : ℕ) → (p : S i) → Ω → ZMod p.val) (j : ℕ) (X : Ω → K)
    (ε H : ℝ) (hX : (1 - ε) * H ≤ entropy X μ)
    (hsmall : (∑ i ∈ I.filter (fun i => i < j),
      ((P i).card : ℝ) * Real.log (2 * B ^ i : ℕ)) ≤ ε * H) :
    (1 - 2 * ε) * H ≤
      condEntropy X (fun ω (i : I.filter (fun i => i < j)) p => Y i.val p ω) μ := by
  have h := smaller_residue_family_condEntropy_ge μ I P S hS B hB hP Y j X
  linarith

end BinaryFormMoat.GeometryIntegration
#print axioms BinaryFormMoat.GeometryIntegration.selected_prime_batch_entropy_le
#print axioms BinaryFormMoat.GeometryIntegration.smaller_residue_family_entropy_le
#print axioms BinaryFormMoat.GeometryIntegration.smaller_residue_family_condEntropy_ge
#print axioms BinaryFormMoat.GeometryIntegration.smaller_residue_family_condEntropy_accuracy
