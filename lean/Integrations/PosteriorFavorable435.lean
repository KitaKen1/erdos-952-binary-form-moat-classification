import Integrations.ConditionalAverage435
import Integrations.SubsetSampling435

noncomputable section
open scoped Classical
namespace BinaryFormMoat.EntropyIntegration
open MeasureTheory ProbabilityTheory

/-- Unfavorable selected coordinates after conditioning on the ACTUAL
finite residue data. No independence of those data and the exact time is used. -/
def posteriorUnfavorable {Ω D C : Type*} [MeasurableSpace Ω] [Fintype C]
    (μ : Measure Ω) (V : Ω → D) (a : D) (S : Finset C) (E : C → Set Ω) : Finset C :=
  S.filter (fun i => (1 : ℝ) / 2 < fiberConditionalReal μ V a (E i))

theorem posteriorUnfavorable_card_le {Ω D C : Type*} [MeasurableSpace Ω] [Fintype C]
    (μ : Measure Ω) (V : Ω → D) (a : D) (S : Finset C) (E : C → Set Ω) :
    ((posteriorUnfavorable μ V a S E).card : ℝ) ≤
      2 * ∑ i ∈ S, fiberConditionalReal μ V a (E i) := by
  let B := posteriorUnfavorable μ V a S E
  calc
    _ = ∑ _i ∈ B, (1 : ℝ) := by simp [B]
    _ ≤ ∑ i ∈ B, 2 * fiberConditionalReal μ V a (E i) := by
      apply Finset.sum_le_sum
      intro i hi
      have h := (Finset.mem_filter.mp hi).2
      linarith
    _ ≤ ∑ i ∈ S, 2 * fiberConditionalReal μ V a (E i) :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
        (fun i _ _ => mul_nonneg (by norm_num) measureReal_nonneg)
    _ = _ := (Finset.mul_sum _ _ _).symm

/-- Exact tower formula bounds the expected posterior bad count, including
zero-mass branches. Independence is NOT an input. -/
theorem posteriorUnfavorable_expected_card_le {Ω D C : Type*} [MeasurableSpace Ω]
    [Fintype D] [MeasurableSpace D] [MeasurableSingletonClass D] [Fintype C]
    (μ : Measure Ω) [IsFiniteMeasure μ] (V : Ω → D) (hV : Measurable V)
    (S : Finset C) (E : C → Set Ω) (hE : ∀ i, MeasurableSet (E i)) :
    (∑ a, μ.real (V ⁻¹' {a}) * ((posteriorUnfavorable μ V a S E).card : ℝ)) ≤
      2 * ∑ i ∈ S, μ.real (E i) := by
  calc
    _ ≤ ∑ a, μ.real (V ⁻¹' {a}) * (2 * ∑ i ∈ S, fiberConditionalReal μ V a (E i)) :=
      Finset.sum_le_sum fun a _ => mul_le_mul_of_nonneg_left
        (posteriorUnfavorable_card_le μ V a S E) measureReal_nonneg
    _ = ∑ a, ∑ i ∈ S, 2 * (μ.real (V ⁻¹' {a}) * fiberConditionalReal μ V a (E i)) := by
      apply Finset.sum_congr rfl
      intro a _
      simp only [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      ring
    _ = ∑ i ∈ S, ∑ a, 2 * (μ.real (V ⁻¹' {a}) * fiberConditionalReal μ V a (E i)) := Finset.sum_comm
    _ = _ := by
      simp_rw [← Finset.mul_sum, ← measureReal_eq_sum_fiberConditionalReal μ V hV _ (hE _)]

/-- The paper's 2*eta*q bound, allowing residue data to depend on BOTH
the chosen subset and all root labels. Auxiliary choices remain OUTSIDE
entropy. Prior bad events may depend on the coordinate/root, not on those data. -/
theorem subsetLabelAverage_posteriorUnfavorable_le {Ω D ι Q : Type*}
    [Fintype Ω] [MeasurableSpace Ω] [MeasurableSingletonClass Ω]
    [Fintype D] [MeasurableSpace D] [MeasurableSingletonClass D]
    [Fintype ι] [DecidableEq ι] [Fintype Q] [Nonempty Q]
    [MeasurableSpace Q] [MeasurableSingletonClass Q]
    (μ : Measure Ω) [IsFiniteMeasure μ] (s : ℕ) (hs : 1 ≤ s) (hsk : s ≤ Fintype.card ι)
    (V : Finset ι → (ι → Q) → Ω → D) (E : ι → Q → Set Ω) (η : ℝ)
    (hbad : (∑ i, ∑ r, μ.real (E i r)) / (Fintype.card ι * (Fintype.card Q : ℝ)) ≤ η) :
    subsetLabelAverage s (fun S ρ => ∑ a, μ.real ((V S ρ) ⁻¹' {a}) *
      ((posteriorUnfavorable μ (V S ρ) a S (fun i => E i (ρ i))).card : ℝ)) ≤ 2 * η * s := by
  apply (subsetLabelAverage_mono s _
    (fun S ρ => ∑ i ∈ S, 2 * μ.real (E i (ρ i))) ?_).trans
  · rw [subsetLabelAverage_sum s hs hsk (fun i r => 2 * μ.real (E i r))]
    have he : ((s : ℝ) / (Fintype.card ι * (Fintype.card Q : ℝ))) *
        (∑ i, ∑ r, 2 * μ.real (E i r)) =
        2 * s * ((∑ i, ∑ r, μ.real (E i r)) / (Fintype.card ι * (Fintype.card Q : ℝ))) := by
      simp_rw [← Finset.mul_sum]
      ring
    rw [he]
    exact (mul_le_mul_of_nonneg_left hbad (by positivity : 0 ≤ 2 * (s : ℝ))).trans_eq (by ring)
  · intro S _ ρ
    simpa only [Finset.mul_sum] using posteriorUnfavorable_expected_card_le μ (V S ρ)
      (measurable_of_finite _) S (fun i => E i (ρ i)) (fun _ => (Set.toFinite _).measurableSet)

end BinaryFormMoat.EntropyIntegration
#print axioms BinaryFormMoat.EntropyIntegration.posteriorUnfavorable
#print axioms BinaryFormMoat.EntropyIntegration.posteriorUnfavorable_card_le
#print axioms BinaryFormMoat.EntropyIntegration.posteriorUnfavorable_expected_card_le
#print axioms BinaryFormMoat.EntropyIntegration.subsetLabelAverage_posteriorUnfavorable_le
