import Integrations.BatchAverage435
import Integrations.BatchRetainedEntropy435
import Integrations.NormalizedEnrichment435
import Integrations.MixedCoordinateFloor435

noncomputable section
namespace BinaryFormMoat.GeometryIntegration
open EntropyIntegration MeasureTheory ProbabilityTheory

section Coordinates
variable {ι R : Type*} [Fintype ι] [DecidableEq ι] [Fintype R]
  (K : ι → Type*) [∀ i, AddCommGroup (K i)] [∀ i, Fintype (K i)]
  [∀ i, MeasurableSpace (K i)] [∀ i, MeasurableSingletonClass (K i)]
  (F : ∀ i, R → Point →+ K i)

omit [DecidableEq ι] [∀ i, Fintype (K i)] [∀ i, MeasurableSingletonClass (K i)] in
theorem labelledPointEntropyMean_nonneg {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (b : ℕ) (X : Ω → Point) :
    0 ≤ labelledPointEntropyMean K F μ b X := by
  unfold labelledPointEntropyMean subsetLabelAverage
  apply div_nonneg _ (Nat.cast_nonneg _)
  apply Finset.sum_nonneg
  intro S _
  apply div_nonneg _ (Nat.cast_nonneg _)
  exact Finset.sum_nonneg (fun _ _ => entropy_nonneg _ _)

section Source
variable {Ω : Type*} [Fintype Ω] [MeasurableSpace Ω] [MeasurableSingletonClass Ω]
  (μ : Measure Ω) [IsProbabilityMeasure μ]

/-- Exact mean of fresh endpoint coordinates in nested batches is q-b
 times the GLOBAL subset-entropy increment. -/
theorem batch_fresh_endpoint_entropy_sum (b q : ℕ) (hbq : b < q)
    (hqk : q ≤ Fintype.card ι) (X : Ω → Point) :
    batchPrefixLabelAverage b q (fun Q S ρ => ∑ i ∈ Q \ S,
      condEntropy (fun ω => F i (ρ i) (X ω)) (residuePrefix K (fun i => F i (ρ i)) S X) μ) =
      (q - b : ℕ) *
        (labelledPointEntropyMean K F μ (b + 1) X - labelledPointEntropyMean K F μ b X) := by
  classical
  rw [batchPrefixLabelAverage_fresh_sum b q hbq hqk]
  have h : subsetLabelAverage b (fun S ρ => ∑ i ∈ Finset.univ \ S,
      condEntropy (fun ω => F i (ρ i) (X ω)) (residuePrefix K (fun i => F i (ρ i)) S X) μ) /
      (Fintype.card ι - b : ℕ) =
      labelledPointEntropyMean K F μ (b + 1) X - labelledPointEntropyMean K F μ b X := by
    rw [← subsetLabelAverage_div]
    exact labelledSubsetEntropy_average_fresh K μ (fun i r ω => F i r (X ω))
      (fun _ _ => measurable_of_finite _) b (by omega)
  calc
    _ = (q - b : ℕ) * (subsetLabelAverage b (fun S ρ => ∑ i ∈ Finset.univ \ S,
        condEntropy (fun ω => F i (ρ i) (X ω)) (residuePrefix K (fun i => F i (ρ i)) S X) μ) /
        (Fintype.card ι - b : ℕ)) := by ring
    _ = _ := by rw [h]

variable [Nonempty R]

/-- Average actual outer-batch budgets FIRST. The geometric floor stays a
 global average, while the starting q-tuple entropy is retained exactly. -/
theorem walk_batch_retained_enrichment_budget (b q : ℕ) (hbq : b < q)
    (hqk : q ≤ Fintype.card ι) (z : ℕ → Point) (D N : ℕ)
    (hstep : ∀ t, |(z (t + 1)).1 - (z t).1| ≤ D ∧ |(z (t + 1)).2 - (z t).2| ≤ D)
    (t u v : Ω → ℕ) (htu : ∀ ω, t ω ≤ u ω) (hu : ∀ ω, u ω ≤ t ω + N)
    (htv : ∀ ω, t ω ≤ v ω) (hv : ∀ ω, v ω ≤ t ω + N)
    (Lw : ℝ) (hN : Real.log (N + 1 : ℕ) ≤ Lw) (T : ℕ)
    (hcard : ∀ i, Fintype.card (K i) ≤ 2 * T) :
    ((q - b : ℕ) / (Fintype.card ι - b : ℕ) : ℝ) *
      labelledPointDifferenceFloor K F μ b (fun ω => z (u ω)) (fun ω => z (v ω)) +
      labelledPointEntropyMean K F μ q (fun ω => z (t ω)) -
      (4 * Lw + 4 * Real.log (4 * D + 1 : ℕ) + 2 * (b : ℝ) * Real.log (2 * T : ℕ)) ≤
    (q - b : ℕ) *
      ((labelledPointEntropyMean K F μ (b + 1) (fun ω => z (u ω)) -
        labelledPointEntropyMean K F μ b (fun ω => z (u ω))) +
       (labelledPointEntropyMean K F μ (b + 1) (fun ω => z (v ω)) -
        labelledPointEntropyMean K F μ b (fun ω => z (v ω)))) := by
  classical
  let X := fun ω => z (u ω)
  let Y := fun ω => z (v ω)
  let Z := fun ω => z (t ω)
  let G := fun (Q S : Finset ι) (ρ : ι → R) => ∑ i ∈ Q \ S,
    condEntropy (fun ω => F i (ρ i) (X ω - Y ω))
      (fun ω => (residuePrefix K (fun i => F i (ρ i)) S X ω,
        residuePrefix K (fun i => F i (ρ i)) S Y ω)) μ
  let H := fun (Q : Finset ι) (ρ : ι → R) => subsetEntropy K μ (fun i ω => F i (ρ i) (Z ω)) Q
  let E := fun (P : Ω → Point) (Q S : Finset ι) (ρ : ι → R) => ∑ i ∈ Q \ S,
    condEntropy (fun ω => F i (ρ i) (P ω)) (residuePrefix K (fun i => F i (ρ i)) S P) μ
  let C := 4 * Lw + 4 * Real.log (4 * D + 1 : ℕ) + 2 * (b : ℝ) * Real.log (2 * T : ℕ)
  have hpoint : ∀ Q ∈ (Finset.univ : Finset ι).powersetCard q,
      ∀ S ∈ Q.powersetCard b, ∀ ρ, G Q S ρ + H Q ρ - C ≤ E X Q S ρ + E Y Q S ρ := by
    intro Q _ S hS ρ
    have h := walk_subset_window_numeric_budget μ K (fun i => F i (ρ i)) Q S
      z D N hstep t u v htu hu htv hv Lw hN T (fun i _ => hcard i)
    rw [(Finset.mem_powersetCard.mp hS).2, Finset.sum_add_distrib] at h
    exact h
  have hmean := batchPrefixLabelAverage_mono b q _ _ hpoint
  rw [batchPrefixLabelAverage_sub, batchPrefixLabelAverage_add,
    batchPrefixLabelAverage_ignore_prefix b q (Nat.le_of_lt hbq),
    batchPrefixLabelAverage_const b q (Nat.le_of_lt hbq) hqk,
    batchPrefixLabelAverage_add] at hmean
  have hG : batchPrefixLabelAverage b q G =
      ((q - b : ℕ) / (Fintype.card ι - b : ℕ) : ℝ) * labelledPointDifferenceFloor K F μ b X Y :=
    batchPrefixLabelAverage_fresh_sum b q hbq hqk _
  have hE (P : Ω → Point) : batchPrefixLabelAverage b q (E P) =
      (q - b : ℕ) * (labelledPointEntropyMean K F μ (b + 1) P - labelledPointEntropyMean K F μ b P) :=
    batch_fresh_endpoint_entropy_sum K F μ b q hbq hqk P
  rw [hG, hE X, hE Y] at hmean
  change _ + labelledPointEntropyMean K F μ q Z - C ≤ _ at hmean
  change _ + labelledPointEntropyMean K F μ q Z - C ≤ _
  convert hmean using 1
  ring

end Source
end Coordinates

/-- Paper's normalized enrichment with a random outer q-batch. Its prior is
E_q(Z), while the geometric floor is only the correctly averaged G_b. -/
theorem labelledPoint_batch_normalized_enrichment
    {Ω Ξ ι R : Type*} [Fintype Ω] [MeasurableSpace Ω] [MeasurableSingletonClass Ω]
    [MeasurableSpace Ξ] [Fintype ι] [DecidableEq ι] [Fintype R]
    (K : ι → Type*) [∀ i, AddCommGroup (K i)] [∀ i, Fintype (K i)]
    [∀ i, MeasurableSpace (K i)] [∀ i, MeasurableSingletonClass (K i)]
    (F : ∀ i, R → Point →+ K i) (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ν : Measure Ξ) (X Y Z : Ω → Point) (V : Ξ → Point)
    (b q : ℕ) (hb : 0 < b) (hbq : b < q) (hqk : q ≤ Fintype.card ι)
    (L C : ℝ) (hL : 0 < L)
    (hfloor : (Fintype.card ι - b : ℕ) * L ≤ labelledPointDifferenceFloor K F μ b X Y)
    (hbudget : ((q - b : ℕ) / (Fintype.card ι - b : ℕ) : ℝ) *
        labelledPointDifferenceFloor K F μ b X Y + labelledPointEntropyMean K F μ q Z - C ≤
      (q - b : ℕ) *
        ((labelledPointEntropyMean K F μ (b + 1) X - labelledPointEntropyMean K F μ b X) +
         (labelledPointEntropyMean K F μ (b + 1) Y - labelledPointEntropyMean K F μ b Y)))
    (hfair : (labelledPointEntropyMean K F μ b X + labelledPointEntropyMean K F μ b Y) / 2 ≤
      labelledPointEntropyMean K F ν b V) :
    (1 + labelledPointEntropyMean K F μ q Z / ((q : ℝ) * L)) / 2 -
      C / (2 * (q - b : ℕ) * L) ≤ labelledPointEntropyMean K F ν b V / ((b : ℝ) * L) := by
  have hx := labelledSubsetEntropy_forward_increment_le K μ
    (fun i r ω => F i r (X ω)) (fun _ _ => measurable_of_finite _) b hb (by omega)
  have hy := labelledSubsetEntropy_forward_increment_le K μ
    (fun i r ω => F i r (Y ω)) (fun _ _ => measurable_of_finite _) b hb (by omega)
  have hscale : (q - b : ℕ) * L ≤
      ((q - b : ℕ) / (Fintype.card ι - b : ℕ) : ℝ) * labelledPointDifferenceFloor K F μ b X Y := by
    have hc : ((Fintype.card ι - b : ℕ) : ℝ) ≠ 0 := by
      exact_mod_cast (Nat.sub_pos_of_lt (by omega : b < Fintype.card ι)).ne'
    have h := mul_le_mul_of_nonneg_left hfloor
      (div_nonneg (Nat.cast_nonneg (q - b)) (Nat.cast_nonneg (Fintype.card ι - b)))
    have he : ((q - b : ℕ) / (Fintype.card ι - b : ℕ) : ℝ) * ((Fintype.card ι - b : ℕ) * L) =
        (q - b : ℕ) * L := by field_simp
    rw [he] at h
    exact h
  apply normalized_enrichment_of_budget b q hb hbq L _ C
    (labelledPointEntropyMean K F μ b X) (labelledPointEntropyMean K F μ b Y)
    (labelledPointEntropyMean K F ν b V)
    (labelledPointEntropyMean K F μ (b + 1) X - labelledPointEntropyMean K F μ b X)
    (labelledPointEntropyMean K F μ (b + 1) Y - labelledPointEntropyMean K F μ b Y)
    hL (labelledPointEntropyMean_nonneg K F μ q Z) _ hx hy hfair
  linarith

/-- The actual forward-window budget is discharged here, rather than
left as an assumed scalar entropy inequality. -/
theorem walk_batch_normalized_enrichment
    {Ω Ξ ι R : Type*} [Fintype Ω] [MeasurableSpace Ω] [MeasurableSingletonClass Ω]
    [MeasurableSpace Ξ] [Fintype ι] [DecidableEq ι] [Fintype R] [Nonempty R]
    (K : ι → Type*) [∀ i, AddCommGroup (K i)] [∀ i, Fintype (K i)]
    [∀ i, MeasurableSpace (K i)] [∀ i, MeasurableSingletonClass (K i)]
    (F : ∀ i, R → Point →+ K i) (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ν : Measure Ξ) (V : Ξ → Point) (b q : ℕ) (hb : 0 < b) (hbq : b < q)
    (hqk : q ≤ Fintype.card ι) (z : ℕ → Point) (D N : ℕ)
    (hstep : ∀ t, |(z (t + 1)).1 - (z t).1| ≤ D ∧ |(z (t + 1)).2 - (z t).2| ≤ D)
    (t u v : Ω → ℕ) (htu : ∀ ω, t ω ≤ u ω) (hu : ∀ ω, u ω ≤ t ω + N)
    (htv : ∀ ω, t ω ≤ v ω) (hv : ∀ ω, v ω ≤ t ω + N)
    (Lw : ℝ) (hN : Real.log (N + 1 : ℕ) ≤ Lw) (T : ℕ)
    (hcard : ∀ i, Fintype.card (K i) ≤ 2 * T) (L : ℝ) (hL : 0 < L)
    (hfloor : (Fintype.card ι - b : ℕ) * L ≤
      labelledPointDifferenceFloor K F μ b (fun ω => z (u ω)) (fun ω => z (v ω)))
    (hfair : (labelledPointEntropyMean K F μ b (fun ω => z (u ω)) +
      labelledPointEntropyMean K F μ b (fun ω => z (v ω))) / 2 ≤
        labelledPointEntropyMean K F ν b V) :
    (1 + labelledPointEntropyMean K F μ q (fun ω => z (t ω)) / ((q : ℝ) * L)) / 2 -
      (4 * Lw + 4 * Real.log (4 * D + 1 : ℕ) + 2 * (b : ℝ) * Real.log (2 * T : ℕ)) /
        (2 * (q - b : ℕ) * L) ≤ labelledPointEntropyMean K F ν b V / ((b : ℝ) * L) := by
  apply labelledPoint_batch_normalized_enrichment K F μ ν
    (fun ω => z (u ω)) (fun ω => z (v ω)) (fun ω => z (t ω)) V b q hb hbq hqk L _ hL
    hfloor _ hfair
  exact walk_batch_retained_enrichment_budget K F μ b q hbq hqk z D N
    hstep t u v htu hu htv hv Lw hN T hcard

end BinaryFormMoat.GeometryIntegration

#print axioms BinaryFormMoat.GeometryIntegration.labelledPointEntropyMean_nonneg
#print axioms BinaryFormMoat.GeometryIntegration.batch_fresh_endpoint_entropy_sum
#print axioms BinaryFormMoat.GeometryIntegration.walk_batch_retained_enrichment_budget
#print axioms BinaryFormMoat.GeometryIntegration.labelledPoint_batch_normalized_enrichment
#print axioms BinaryFormMoat.GeometryIntegration.walk_batch_normalized_enrichment
