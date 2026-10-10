import Integrations.PosteriorFavorable435

noncomputable section
open scoped Classical
namespace BinaryFormMoat.EntropyIntegration
open MeasureTheory ProbabilityTheory

/-- Bad ORIGINAL data branches for one fixed failure event. -/
def posteriorBadData {Ω D : Type*} [MeasurableSpace Ω] [Fintype D]
    (μ : Measure Ω) (V : Ω → D) (E : Set Ω) : Finset D :=
  Finset.univ.filter (fun a => (1 : ℝ) / 2 < fiberConditionalReal μ V a E)

theorem posteriorBadData_favorable {Ω D : Type*} [MeasurableSpace Ω] [Fintype D]
    (μ : Measure Ω) (V : Ω → D) (E : Set Ω) (a : D)
    (ha : a ∉ posteriorBadData μ V E) :
    fiberConditionalReal μ V a E ≤ (1 : ℝ) / 2 := by
  simpa [posteriorBadData, not_lt] using ha

/-- Tower/Markov under the ORIGINAL law. Different coordinates may use
different data maps; no conditional independence or common data is needed.
Zero-mass original fibers contribute exactly zero. -/
theorem posteriorBadData_mass_le {Ω D : Type*} [MeasurableSpace Ω]
    [Fintype D] [MeasurableSpace D] [MeasurableSingletonClass D]
    (μ : Measure Ω) [IsFiniteMeasure μ] (V : Ω → D) (hV : Measurable V)
    (E : Set Ω) (hE : MeasurableSet E) :
    μ.real (V ⁻¹' (posteriorBadData μ V E : Set D)) ≤ 2 * μ.real E := by
  rw [← sum_measureReal_preimage_singleton (posteriorBadData μ V E)
    (fun a _ => hV (MeasurableSet.singleton a))]
  calc
    _ ≤ ∑ a ∈ posteriorBadData μ V E,
        2 * (μ.real (V ⁻¹' {a}) * fiberConditionalReal μ V a E) := by
      apply Finset.sum_le_sum
      intro a ha
      have hp := (Finset.mem_filter.mp ha).2
      have hw : 0 ≤ μ.real (V ⁻¹' {a}) := measureReal_nonneg
      nlinarith
    _ ≤ ∑ a, 2 * (μ.real (V ⁻¹' {a}) * fiberConditionalReal μ V a E) :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
        (fun a _ _ => mul_nonneg (by norm_num) (mul_nonneg measureReal_nonneg measureReal_nonneg))
    _ = _ := by rw [← Finset.mul_sum, ← measureReal_eq_sum_fiberConditionalReal μ V hV E hE]

/-- Arbitrary coordinate-dependent and auxiliary-dependent data, including
different finite alphabets at different coordinates. The subset/root choices
stay outside the source probability law. -/
theorem subsetLabelAverage_coordinateBadData_le {Ω ι Q : Type*}
    [Fintype Ω] [MeasurableSpace Ω] [MeasurableSingletonClass Ω]
    [Fintype ι] [DecidableEq ι] [Fintype Q] [Nonempty Q]
    [MeasurableSpace Q] [MeasurableSingletonClass Q]
    (D : ι → Type*) [∀ i, Fintype (D i)] [∀ i, MeasurableSpace (D i)]
    [∀ i, MeasurableSingletonClass (D i)]
    (μ : Measure Ω) [IsFiniteMeasure μ] (s : ℕ) (hs : 1 ≤ s) (hsk : s ≤ Fintype.card ι)
    (V : Finset ι → (ι → Q) → ∀ i, Ω → D i) (E : ι → Q → Set Ω) (η : ℝ)
    (hbad : (∑ i, ∑ r, μ.real (E i r)) / (Fintype.card ι * (Fintype.card Q : ℝ)) ≤ η) :
    subsetLabelAverage s (fun S ρ => ∑ i ∈ S,
      μ.real ((V S ρ i) ⁻¹' (posteriorBadData μ (V S ρ i) (E i (ρ i)) : Set (D i)))) ≤
      2 * η * s := by
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
    exact Finset.sum_le_sum fun i _ => posteriorBadData_mass_le μ (V S ρ i)
      (measurable_of_finite _) (E i (ρ i)) (Set.toFinite _).measurableSet

/-- In information bounds the same original bad probabilities multiply
logarithmic costs. Uniformly bounded nonnegative costs can be averaged
without selecting one common posterior or moving choices inside entropy. -/
theorem subsetLabelAverage_coordinateBadData_cost_le {Ω ι Q : Type*}
    [Fintype Ω] [MeasurableSpace Ω] [MeasurableSingletonClass Ω]
    [Fintype ι] [DecidableEq ι] [Fintype Q] [Nonempty Q]
    [MeasurableSpace Q] [MeasurableSingletonClass Q]
    (D : ι → Type*) [∀ i, Fintype (D i)] [∀ i, MeasurableSpace (D i)]
    [∀ i, MeasurableSingletonClass (D i)]
    (μ : Measure Ω) [IsFiniteMeasure μ] (s : ℕ) (hs : 1 ≤ s) (hsk : s ≤ Fintype.card ι)
    (V : Finset ι → (ι → Q) → ∀ i, Ω → D i) (E : ι → Q → Set Ω) (η K : ℝ)
    (hK : 0 ≤ K) (cost : Finset ι → (ι → Q) → ι → ℝ)
    (hcost : ∀ S ρ i, cost S ρ i ≤ K)
    (hbad : (∑ i, ∑ r, μ.real (E i r)) / (Fintype.card ι * (Fintype.card Q : ℝ)) ≤ η) :
    subsetLabelAverage s (fun S ρ => ∑ i ∈ S,
      μ.real ((V S ρ i) ⁻¹' (posteriorBadData μ (V S ρ i) (E i (ρ i)) : Set (D i))) *
        cost S ρ i) ≤ 2 * η * s * K := by
  apply (subsetLabelAverage_mono s _ (fun S ρ => ∑ i ∈ S,
    μ.real ((V S ρ i) ⁻¹' (posteriorBadData μ (V S ρ i) (E i (ρ i)) : Set (D i))) * K) ?_).trans
  · convert mul_le_mul_of_nonneg_right
      (subsetLabelAverage_coordinateBadData_le D μ s hs hsk V E η hbad) hK using 1
    unfold subsetLabelAverage
    simp_rw [← Finset.sum_mul]
    simp_rw [← Finset.sum_div]
    simp_rw [← Finset.sum_mul]
    ring
  · intro S _ ρ
    exact Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left (hcost S ρ i) measureReal_nonneg

end BinaryFormMoat.EntropyIntegration
#print axioms BinaryFormMoat.EntropyIntegration.posteriorBadData
#print axioms BinaryFormMoat.EntropyIntegration.posteriorBadData_favorable
#print axioms BinaryFormMoat.EntropyIntegration.posteriorBadData_mass_le
#print axioms BinaryFormMoat.EntropyIntegration.subsetLabelAverage_coordinateBadData_le
#print axioms BinaryFormMoat.EntropyIntegration.subsetLabelAverage_coordinateBadData_cost_le
