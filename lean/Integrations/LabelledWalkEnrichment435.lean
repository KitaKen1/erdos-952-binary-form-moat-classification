import Integrations.LabelledSubsetEntropy435
import Integrations.WalkEnrichmentCost435
import Integrations.FairDifferenceEntropy435

noncomputable section
namespace BinaryFormMoat.GeometryIntegration
open EntropyIntegration MeasureTheory ProbabilityTheory

section Coordinates
variable {ι R : Type*} [Fintype ι] [DecidableEq ι] [Fintype R]
  (K : ι → Type*) [∀ i, AddCommGroup (K i)] [∀ i, Fintype (K i)]
  [∀ i, MeasurableSpace (K i)] [∀ i, MeasurableSingletonClass (K i)]
  (F : ∀ i, R → Point →+ K i)

/-- Fixed-subset entropy, averaged over distinct prime indices and uniform root labels. -/
def labelledPointEntropyMean {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (s : ℕ) (X : Ω → Point) : ℝ :=
  subsetLabelAverage s (fun A ρ => subsetEntropy K μ (fun i ω => F i (ρ i) (X ω)) A)

/-- Full starting tuple entropy averaged only over the independent root labels. -/
def labelledPointFullEntropyMean {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (Z : Ω → Point) : ℝ := by
  classical
  exact (∑ ρ : ι → R, entropy (fun ω i => F i (ρ i) (Z ω)) μ) / Fintype.card (ι → R)

def labelledPointDifferenceFloor {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (s : ℕ) (X Y : Ω → Point) : ℝ :=
  subsetLabelAverage s (fun A ρ => ∑ i ∈ Finset.univ \ A,
    condEntropy (fun ω => F i (ρ i) (X ω - Y ω))
      (fun ω => (residuePrefix K (fun i => F i (ρ i)) A X ω,
        residuePrefix K (fun i => F i (ρ i)) A Y ω)) μ)

omit [∀ i, Fintype (K i)] [∀ i, MeasurableSingletonClass (K i)] in
theorem labelledPointFullEntropyMean_nonneg {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (Z : Ω → Point) : 0 ≤ labelledPointFullEntropyMean K F μ Z := by
  unfold labelledPointFullEntropyMean
  exact div_nonneg (Finset.sum_nonneg (fun _ _ => entropy_nonneg _ _)) (Nat.cast_nonneg _)

section Walk
variable {Ω : Type*} [Fintype Ω] [MeasurableSpace Ω] [MeasurableSingletonClass Ω]
  [Nonempty R] (μ : Measure Ω) [IsProbabilityMeasure μ]

/-- The retained-information budget averaged on the exact original law.
The physical costs are derived from the actual common forward walk window. -/
theorem walk_labelled_retained_enrichment_budget (b : ℕ) (hb : b < Fintype.card ι)
    (z : ℕ → Point) (D N : ℕ)
    (hstep : ∀ t, |(z (t + 1)).1 - (z t).1| ≤ D ∧ |(z (t + 1)).2 - (z t).2| ≤ D)
    (t u v : Ω → ℕ) (htu : ∀ ω, t ω ≤ u ω) (hu : ∀ ω, u ω ≤ t ω + N)
    (htv : ∀ ω, t ω ≤ v ω) (hv : ∀ ω, v ω ≤ t ω + N)
    (Lw : ℝ) (hN : Real.log (N + 1 : ℕ) ≤ Lw) (T : ℕ)
    (hcard : ∀ i, Fintype.card (K i) ≤ 2 * T) :
    labelledPointDifferenceFloor K F μ b (fun ω => z (u ω)) (fun ω => z (v ω)) +
      labelledPointFullEntropyMean K F μ (fun ω => z (t ω)) -
        (4 * Lw + 4 * Real.log (4 * D + 1 : ℕ) + 2 * (b : ℝ) * Real.log (2 * T : ℕ)) ≤
      (Fintype.card ι - b : ℕ) *
        ((labelledPointEntropyMean K F μ (b + 1) (fun ω => z (u ω)) -
          labelledPointEntropyMean K F μ b (fun ω => z (u ω))) +
         (labelledPointEntropyMean K F μ (b + 1) (fun ω => z (v ω)) -
          labelledPointEntropyMean K F μ b (fun ω => z (v ω)))) := by
  classical
  let X : Ω → Point := fun ω => z (u ω)
  let Y : Ω → Point := fun ω => z (v ω)
  let Z : Ω → Point := fun ω => z (t ω)
  let G := fun (A : Finset ι) (ρ : ι → R) => ∑ i ∈ Finset.univ \ A,
    condEntropy (fun ω => F i (ρ i) (X ω - Y ω))
      (fun ω => (residuePrefix K (fun i => F i (ρ i)) A X ω,
        residuePrefix K (fun i => F i (ρ i)) A Y ω)) μ
  let H := fun (ρ : ι → R) => entropy (fun ω i => F i (ρ i) (Z ω)) μ
  let C := 4 * Lw + 4 * Real.log (4 * D + 1 : ℕ) + 2 * (b : ℝ) * Real.log (2 * T : ℕ)
  let E := fun (P : Ω → Point) (A : Finset ι) (ρ : ι → R) =>
    ∑ i ∈ Finset.univ \ A,
      condEntropy (fun ω => F i (ρ i) (P ω)) (residuePrefix K (fun i => F i (ρ i)) A P) μ
  have hpoint : ∀ A ∈ (Finset.univ : Finset ι).powersetCard b, ∀ ρ,
      G A ρ + H ρ - C ≤ E X A ρ + E Y A ρ := by
    intro A hA ρ
    have hAc := (Finset.mem_powersetCard.mp hA).2
    have h := walk_window_retained_enrichment_numeric_budget μ K (fun i => F i (ρ i))
      A z D N hstep t u v htu hu htv hv (G A ρ) Lw hN T (fun i _ => hcard i) le_rfl
    rw [hAc, Finset.sum_add_distrib] at h
    change G A ρ + H ρ - 4 * Lw - 4 * Real.log (4 * D + 1 : ℕ) -
      2 * (b : ℝ) * Real.log (2 * T : ℕ) ≤ E X A ρ + E Y A ρ at h
    change G A ρ + H ρ - (4 * Lw + 4 * Real.log (4 * D + 1 : ℕ) +
      2 * (b : ℝ) * Real.log (2 * T : ℕ)) ≤ E X A ρ + E Y A ρ
    linarith
  have hmean := subsetLabelAverage_mono b _ _ hpoint
  rw [subsetLabelAverage_sub, subsetLabelAverage_add,
    subsetLabelAverage_ignore_subset b (Nat.le_of_lt hb),
    subsetLabelAverage_const b (Nat.le_of_lt hb), subsetLabelAverage_add] at hmean
  have hE (P : Ω → Point) : subsetLabelAverage b (E P) /
      (Fintype.card ι - b : ℕ) = labelledPointEntropyMean K F μ (b + 1) P -
        labelledPointEntropyMean K F μ b P := by
    rw [← subsetLabelAverage_div]
    exact labelledSubsetEntropy_average_fresh K μ (fun i r ω => F i r (P ω))
      (fun _ _ => measurable_of_finite _) b hb
  have hc : ((Fintype.card ι - b : ℕ) : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.sub_pos_of_lt hb).ne'
  have hx := (div_eq_iff hc).mp (hE X)
  have hy := (div_eq_iff hc).mp (hE Y)
  rw [hx, hy] at hmean
  change labelledPointDifferenceFloor K F μ b X Y + labelledPointFullEntropyMean K F μ Z - C ≤ _
  change labelledPointDifferenceFloor K F μ b X Y + labelledPointFullEntropyMean K F μ Z - C ≤
    (labelledPointEntropyMean K F μ (b + 1) X - labelledPointEntropyMean K F μ b X) *
      (Fintype.card ι - b : ℕ) +
    (labelledPointEntropyMean K F μ (b + 1) Y - labelledPointEntropyMean K F μ b Y) *
      (Fintype.card ι - b : ℕ) at hmean
  convert hmean using 1
  ring

end Walk

/-- The concrete fair difference-endpoint law supplies the mixture step for every subset. -/
theorem differenceEndpoint_labelledPointEntropyMean_ge_half (z : ℕ → Point) (N b : ℕ) :
    (labelledPointEntropyMean K F (uniformOn (Set.univ : Set (WalkDifferences z N))) b
        (fun h => z (walkDifferenceTimes z N h).1.val) +
     labelledPointEntropyMean K F (uniformOn (Set.univ : Set (WalkDifferences z N))) b
        (fun h => z (walkDifferenceTimes z N h).2.val)) / 2 ≤
      labelledPointEntropyMean K F (differenceEndpointSourceLaw z N) b
        (fun s => z (differenceEndpointIndex z N s).val) := by
  rw [labelledPointEntropyMean, labelledPointEntropyMean, labelledPointEntropyMean,
    ← subsetLabelAverage_add, ← subsetLabelAverage_div]
  apply subsetLabelAverage_mono
  intro A _ ρ
  exact differenceEndpoint_entropy_ge_half z N (fun p (i : A) => F i.val (ρ i.val) p)

end Coordinates
end BinaryFormMoat.GeometryIntegration

#print axioms BinaryFormMoat.GeometryIntegration.labelledPointEntropyMean
#print axioms BinaryFormMoat.GeometryIntegration.labelledPointFullEntropyMean
#print axioms BinaryFormMoat.GeometryIntegration.labelledPointDifferenceFloor
#print axioms BinaryFormMoat.GeometryIntegration.labelledPointFullEntropyMean_nonneg
#print axioms BinaryFormMoat.GeometryIntegration.walk_labelled_retained_enrichment_budget
#print axioms BinaryFormMoat.GeometryIntegration.differenceEndpoint_labelledPointEntropyMean_ge_half
