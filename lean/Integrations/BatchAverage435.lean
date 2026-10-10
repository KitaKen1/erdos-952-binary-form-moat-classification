import Integrations.NestedFresh435
import Integrations.LabelledSubsetEntropy435

noncomputable section
namespace BinaryFormMoat.EntropyIntegration

theorem relativeSubsetMean_congr {ι : Type*} (C : Finset ι) (b : ℕ)
    (f g : Finset ι → ℝ) (h : ∀ S ∈ C.powersetCard b, f S = g S) :
    relativeSubsetMean C b f = relativeSubsetMean C b g := by
  unfold relativeSubsetMean
  exact congrArg (fun x : ℝ => x / (C.powersetCard b).card) (Finset.sum_congr rfl h)

/-- Uniform global labels, outer q-batch and inner b-prefix.
The summand may depend on both sets, so a marginal cannot be substituted blindly. -/
def batchPrefixLabelAverage {ι R : Type*} [Fintype ι] [DecidableEq ι] [Fintype R]
    (b q : ℕ) (f : Finset ι → Finset ι → (ι → R) → ℝ) : ℝ :=
  (∑ ρ : ι → R, relativeSubsetMean (Finset.univ : Finset ι) q (fun Q =>
    relativeSubsetMean Q b (fun S => f Q S ρ))) / Fintype.card (ι → R)

theorem batchPrefixLabelAverage_mono {ι R : Type*}
    [Fintype ι] [DecidableEq ι] [Fintype R] (b q : ℕ)
    (f g : Finset ι → Finset ι → (ι → R) → ℝ)
    (h : ∀ Q ∈ (Finset.univ : Finset ι).powersetCard q,
      ∀ S ∈ Q.powersetCard b, ∀ ρ, f Q S ρ ≤ g Q S ρ) :
    batchPrefixLabelAverage b q f ≤ batchPrefixLabelAverage b q g := by
  unfold batchPrefixLabelAverage
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
  apply Finset.sum_le_sum
  intro ρ _
  apply relativeSubsetMean_mono
  intro Q hQ
  exact relativeSubsetMean_mono Q b _ _ (fun S hS => h Q hQ S hS ρ)

theorem batchPrefixLabelAverage_add {ι R : Type*}
    [Fintype ι] [DecidableEq ι] [Fintype R] (b q : ℕ)
    (f g : Finset ι → Finset ι → (ι → R) → ℝ) :
    batchPrefixLabelAverage b q (fun Q S ρ => f Q S ρ + g Q S ρ) =
      batchPrefixLabelAverage b q f + batchPrefixLabelAverage b q g := by
  simp only [batchPrefixLabelAverage, relativeSubsetMean, Finset.sum_add_distrib, add_div]

theorem batchPrefixLabelAverage_sub {ι R : Type*}
    [Fintype ι] [DecidableEq ι] [Fintype R] (b q : ℕ)
    (f g : Finset ι → Finset ι → (ι → R) → ℝ) :
    batchPrefixLabelAverage b q (fun Q S ρ => f Q S ρ - g Q S ρ) =
      batchPrefixLabelAverage b q f - batchPrefixLabelAverage b q g := by
  simp only [batchPrefixLabelAverage, relativeSubsetMean, Finset.sum_sub_distrib, sub_div]

theorem batchPrefixLabelAverage_div {ι R : Type*}
    [Fintype ι] [DecidableEq ι] [Fintype R] (b q : ℕ)
    (f : Finset ι → Finset ι → (ι → R) → ℝ) (c : ℝ) :
    batchPrefixLabelAverage b q (fun Q S ρ => f Q S ρ / c) =
      batchPrefixLabelAverage b q f / c := by
  simp only [batchPrefixLabelAverage, relativeSubsetMean, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro ρ _
  apply Finset.sum_congr rfl
  intro Q _
  apply Finset.sum_congr rfl
  intro S _
  ring

/-- Inner-prefix quantities use their exact uniform global marginal. -/
theorem batchPrefixLabelAverage_ignore_batch {ι R : Type*}
    [Fintype ι] [DecidableEq ι] [Fintype R] (b q : ℕ)
    (hbq : b ≤ q) (hqk : q ≤ Fintype.card ι) (f : Finset ι → (ι → R) → ℝ) :
    batchPrefixLabelAverage b q (fun _ S ρ => f S ρ) = subsetLabelAverage b f := by
  rw [subsetLabelAverage_eq_mean_subsetMean]
  unfold batchPrefixLabelAverage
  congr 1
  apply Finset.sum_congr rfl
  intro ρ _
  simpa only [relativeSubsetMean] using nested_subsetMean_eq b q hbq hqk (fun S => f S ρ)

/-- Starting outer-batch entropy survives prefix averaging exactly. -/
theorem batchPrefixLabelAverage_ignore_prefix {ι R : Type*}
    [Fintype ι] [DecidableEq ι] [Fintype R] (b q : ℕ)
    (hbq : b ≤ q) (f : Finset ι → (ι → R) → ℝ) :
    batchPrefixLabelAverage b q (fun Q _ ρ => f Q ρ) = subsetLabelAverage q f := by
  rw [subsetLabelAverage_eq_mean_subsetMean]
  unfold batchPrefixLabelAverage
  congr 1
  apply Finset.sum_congr rfl
  intro ρ _
  change relativeSubsetMean (Finset.univ : Finset ι) q
    (fun Q => relativeSubsetMean Q b (fun _ => f Q ρ)) =
      relativeSubsetMean (Finset.univ : Finset ι) q (fun Q => f Q ρ)
  apply relativeSubsetMean_congr
  intro Q hQ
  exact relativeSubsetMean_const Q b (by rw [(Finset.mem_powersetCard.mp hQ).2]; exact hbq) _

theorem batchPrefixLabelAverage_const {ι R : Type*}
    [Fintype ι] [DecidableEq ι] [Fintype R] [Nonempty R] (b q : ℕ)
    (hbq : b ≤ q) (hqk : q ≤ Fintype.card ι) (c : ℝ) :
    batchPrefixLabelAverage (ι := ι) (R := R) b q (fun _ _ _ => c) = c := by
  rw [batchPrefixLabelAverage_ignore_batch b q hbq hqk,
    subsetLabelAverage_const b (hbq.trans hqk)]

/-- Exact labelled (prefix,fresh-coordinate) law, not just the prefix marginal. -/
theorem batchPrefixLabelAverage_fresh_mean {ι R : Type*}
    [Fintype ι] [DecidableEq ι] [Fintype R] (b q : ℕ)
    (hbq : b < q) (hqk : q ≤ Fintype.card ι) (w : Finset ι → ι → (ι → R) → ℝ) :
    batchPrefixLabelAverage b q (fun Q S ρ => (∑ j ∈ Q \ S, w S j ρ) / (q - b : ℕ)) =
      subsetLabelAverage b (fun S ρ => (∑ j ∈ Finset.univ \ S, w S j ρ) /
        (Fintype.card ι - b : ℕ)) := by
  rw [subsetLabelAverage_eq_mean_subsetMean]
  unfold batchPrefixLabelAverage
  congr 1
  apply Finset.sum_congr rfl
  intro ρ _
  exact nested_fresh_mean_eq b q hbq hqk (fun S j => w S j ρ)

/-- Unnormalized sums retain the exact (q-b)/(k-b) factor required by enrichment. -/
theorem batchPrefixLabelAverage_fresh_sum {ι R : Type*}
    [Fintype ι] [DecidableEq ι] [Fintype R] (b q : ℕ)
    (hbq : b < q) (hqk : q ≤ Fintype.card ι) (w : Finset ι → ι → (ι → R) → ℝ) :
    batchPrefixLabelAverage b q (fun Q S ρ => ∑ j ∈ Q \ S, w S j ρ) =
      ((q - b : ℕ) / (Fintype.card ι - b : ℕ) : ℝ) *
        subsetLabelAverage b (fun S ρ => ∑ j ∈ Finset.univ \ S, w S j ρ) := by
  have h := batchPrefixLabelAverage_fresh_mean b q hbq hqk w
  rw [batchPrefixLabelAverage_div, subsetLabelAverage_div] at h
  have hc : ((q - b : ℕ) : ℝ) ≠ 0 := by exact_mod_cast (Nat.sub_pos_of_lt hbq).ne'
  have he := (div_eq_iff hc).mp h
  rw [he]
  ring

end BinaryFormMoat.EntropyIntegration

#print axioms BinaryFormMoat.EntropyIntegration.relativeSubsetMean_congr
#print axioms BinaryFormMoat.EntropyIntegration.batchPrefixLabelAverage
#print axioms BinaryFormMoat.EntropyIntegration.batchPrefixLabelAverage_mono
#print axioms BinaryFormMoat.EntropyIntegration.batchPrefixLabelAverage_add
#print axioms BinaryFormMoat.EntropyIntegration.batchPrefixLabelAverage_sub
#print axioms BinaryFormMoat.EntropyIntegration.batchPrefixLabelAverage_div
#print axioms BinaryFormMoat.EntropyIntegration.batchPrefixLabelAverage_ignore_batch
#print axioms BinaryFormMoat.EntropyIntegration.batchPrefixLabelAverage_ignore_prefix
#print axioms BinaryFormMoat.EntropyIntegration.batchPrefixLabelAverage_const
#print axioms BinaryFormMoat.EntropyIntegration.batchPrefixLabelAverage_fresh_mean
#print axioms BinaryFormMoat.EntropyIntegration.batchPrefixLabelAverage_fresh_sum
