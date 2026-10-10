import Integrations.OrderedJointBudget435
import Integrations.PaperJointBatchEntropy435
import Integrations.PaperJointBadGap435

noncomputable section
open scoped Classical
namespace BinaryFormMoat.GeometryIntegration
open EntropyIntegration MeasureTheory ProbabilityTheory

/-- The same true batch mean is used in the favorable-list cost, without
replacing it by log(T) or log(2T). Auxiliary choices stay outside entropy. -/
theorem subsetLabelAverage_root_gap (P : Finset ℕ) {Q : Type*}
    [Fintype Q] [Nonempty Q] [MeasurableSpace Q] [MeasurableSingletonClass Q]
    (s : ℕ) (hs : 1 ≤ s) (hsk : s ≤ P.card) (β : ℝ) :
    subsetLabelAverage (ι := P) (R := Q) s (fun S _ =>
      ∑ p ∈ S, ((1 - β) * Real.log (p.val : ℝ) + Real.log 6)) =
      (1 - β) * ((s : ℝ) * primeBatchLogMean P) + s * Real.log 6 := by
  have hp : (P.card : ℝ) ≠ 0 := by exact_mod_cast (by omega : P.card ≠ 0)
  rw [subsetLabelAverage_sum s hs (by simpa using hsk)
    (fun (p : P) (_r : Q) => (1 - β) * Real.log (p.val : ℝ) + Real.log 6)]
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, Fintype.card_coe]
  rw [← Finset.mul_sum, Finset.sum_add_distrib, ← Finset.mul_sum]
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, Fintype.card_coe]
  have hQ : (Fintype.card Q : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  unfold primeBatchLogMean
  field_simp

/-- Faithful masked targets retain the actual subset conditional entropy
mean on the original checkpoint law. No roots are resampled inside that law. -/
theorem labelledMaskedCondEntropyMean_eq {Ω ι Q U : Type*}
    [Fintype Ω] [MeasurableSpace Ω] [MeasurableSingletonClass Ω]
    [Fintype ι] [DecidableEq ι] [Fintype Q]
    [Fintype U] [AddCommGroup U] [MeasurableSpace U] [MeasurableSingletonClass U]
    (K : ι → Type*) [∀ i, AddCommGroup (K i)] [∀ i, Fintype (K i)]
    [∀ i, MeasurableSpace (K i)] [∀ i, MeasurableSingletonClass (K i)]
    (F : ∀ i, Q → Point →+ K i) (μ : Measure Ω) [IsProbabilityMeasure μ]
    (s : ℕ) (X : Ω → Point) (ψ : Point →+ U) :
    subsetLabelAverage s (fun S ρ => condEntropy
      (fun ω => maskedPriorHom K (fun i => F i (ρ i)) S (X ω))
      (fun ω => ψ (X ω)) μ) =
      labelledPointCondEntropyMean K F μ s X (fun ω => ψ (X ω)) := by
  simp_rw [maskedPriorHom_target_condEntropy K μ X]
  rfl

/-- Average the ACTUAL joint lower bounds before choosing auxiliary subsets
and labels. One physical transport loss is charged per batch, not per prime.
The caller supplies bounds on the original entropy and actual weighted bad
mass; the paper application derives both from its SAME batch certificates. -/
theorem joint_package_average_lower_bound {ι Q : Type*}
    [Fintype ι] [Fintype Q] [Nonempty Q]
    (s : ℕ) (hs : s ≤ Fintype.card ι) (m : ℝ) (hm : 0 < m)
    (H B : Finset ι → (ι → Q) → ℝ) (G I : Finset ι → (ι → Q) → ℝ)
    (h g b C : ℝ)
    (hH : h ≤ subsetLabelAverage s H)
    (hG : subsetLabelAverage s G = g)
    (hB : subsetLabelAverage s B ≤ b)
    (hI : ∀ S ∈ (Finset.univ : Finset ι).powersetCard s, ∀ ρ,
      (H S ρ - (G S ρ + B S ρ)) / m - C ≤ I S ρ) :
    (h - (g + b)) / m - C ≤ subsetLabelAverage s I := by
  have ha := subsetLabelAverage_mono s _ I hI
  rw [subsetLabelAverage_sub, subsetLabelAverage_div, subsetLabelAverage_sub,
    subsetLabelAverage_add, hG, subsetLabelAverage_const s hs C] at ha
  have hn : h - (g + b) ≤ subsetLabelAverage s H - (g + subsetLabelAverage s B) := by linarith
  exact (sub_le_sub_right (div_le_div_of_nonneg_right hn hm.le) C).trans ha

end BinaryFormMoat.GeometryIntegration
#print axioms BinaryFormMoat.GeometryIntegration.subsetLabelAverage_root_gap
#print axioms BinaryFormMoat.GeometryIntegration.labelledMaskedCondEntropyMean_eq
#print axioms BinaryFormMoat.GeometryIntegration.joint_package_average_lower_bound
