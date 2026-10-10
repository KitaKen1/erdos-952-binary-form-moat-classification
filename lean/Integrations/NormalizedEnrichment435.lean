import Integrations.LabelledWalkEnrichment435
import Integrations.NestedSubset435

noncomputable section
namespace BinaryFormMoat.EntropyIntegration

/-- Algebraic normalization of a retained-prior enrichment budget. -/
theorem normalized_enrichment_of_budget (b q : ℕ) (hb : 0 < b) (hbq : b < q)
    (L H C x y v dx dy : ℝ) (hL : 0 < L) (hH : 0 ≤ H)
    (hbudget : (q - b : ℕ) * L + H - C ≤ (q - b : ℕ) * (dx + dy))
    (hx : dx ≤ x / b) (hy : dy ≤ y / b) (hv : (x + y) / 2 ≤ v) :
    (1 + H / ((q : ℝ) * L)) / 2 - C / (2 * (q - b : ℕ) * L) ≤ v / ((b : ℝ) * L) := by
  have hbR : (0 : ℝ) < b := by exact_mod_cast hb
  have hqR : (0 : ℝ) < q := by exact_mod_cast (by omega : 0 < q)
  have hcR : (0 : ℝ) < (q - b : ℕ) := by exact_mod_cast Nat.sub_pos_of_lt hbq
  have hcq : ((q - b : ℕ) : ℝ) ≤ q := by exact_mod_cast Nat.sub_le q b
  have hprior := div_le_div_of_nonneg_left hH hcR hcq
  have hd : L + H / (q - b : ℕ) - C / (q - b : ℕ) ≤ dx + dy := by
    calc
      _ = ((q - b : ℕ) * L + H - C) / (q - b : ℕ) := by field_simp
      _ ≤ ((q - b : ℕ) * (dx + dy)) / (q - b : ℕ) :=
        div_le_div_of_nonneg_right hbudget hcR.le
      _ = _ := mul_div_cancel_left₀ _ hcR.ne'
  have hxy : dx + dy ≤ 2 * v / b := by
    calc
      _ ≤ x / b + y / b := add_le_add hx hy
      _ = (x + y) / b := (add_div _ _ _).symm
      _ ≤ _ := div_le_div_of_nonneg_right (by linarith : x + y ≤ 2 * v) hbR.le
  rw [mul_div_assoc] at hxy
  have hbase : (L + H / q - C / (q - b : ℕ)) / 2 ≤ v / b := by
    linarith
  have hn := div_le_div_of_nonneg_right hbase hL.le
  have he : ((L + H / q - C / (q - b : ℕ)) / 2) / L =
      (1 + H / ((q : ℝ) * L)) / 2 - C / (2 * (q - b : ℕ) * L) := by
    field_simp
  rw [he, div_div] at hn
  exact hn

/-- Exact finite iteration; the known final value determines the short scalar proof. -/
theorem normalized_enrichment_iterate (h : ℕ → ℝ) (ε : ℝ)
    (hstep : ∀ n, (1 + h n) / 2 - ε ≤ h (n + 1)) (n : ℕ) :
    1 - 2 * ε - ((1 - 2 * ε) - h 0) * (1 / 2 : ℝ) ^ n ≤ h n := by
  induction n with
  | zero => simp only [pow_zero, mul_one]; linarith
  | succ n ih =>
    rw [pow_succ]
    have hn := hstep n
    linarith

/-- A nonnegative starting entropy gives the uniform error bound used in a schedule. -/
theorem normalized_enrichment_iterate_nonneg (h : ℕ → ℝ) (ε : ℝ) (hε : 0 ≤ ε)
    (h0 : 0 ≤ h 0) (hstep : ∀ n, (1 + h n) / 2 - ε ≤ h (n + 1)) (n : ℕ) :
    1 - 2 * ε - (1 / 2 : ℝ) ^ n ≤ h n := by
  have hi := normalized_enrichment_iterate h ε hstep n
  have hp : (0 : ℝ) ≤ (1 / 2 : ℝ) ^ n := by positivity
  nlinarith

end BinaryFormMoat.EntropyIntegration

namespace BinaryFormMoat.GeometryIntegration
open EntropyIntegration MeasureTheory ProbabilityTheory

/-- Actual averaged residue entropies satisfy the paper's normalized recurrence
once the geometric difference floor and the checked physical budget are supplied. -/
theorem labelledPoint_normalized_enrichment
    {Ω Ξ ι R : Type*} [Fintype Ω] [MeasurableSpace Ω] [MeasurableSingletonClass Ω]
    [MeasurableSpace Ξ] [Fintype ι] [DecidableEq ι] [Fintype R]
    (K : ι → Type*) [∀ i, AddCommGroup (K i)] [∀ i, Fintype (K i)]
    [∀ i, MeasurableSpace (K i)] [∀ i, MeasurableSingletonClass (K i)]
    (F : ∀ i, R → Point →+ K i) (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ν : Measure Ξ) (X Y Z : Ω → Point) (V : Ξ → Point)
    (b : ℕ) (hb : 0 < b) (hbq : b < Fintype.card ι) (L C : ℝ) (hL : 0 < L)
    (hfloor : (Fintype.card ι - b : ℕ) * L ≤ labelledPointDifferenceFloor K F μ b X Y)
    (hbudget : labelledPointDifferenceFloor K F μ b X Y + labelledPointFullEntropyMean K F μ Z - C ≤
      (Fintype.card ι - b : ℕ) *
        ((labelledPointEntropyMean K F μ (b + 1) X - labelledPointEntropyMean K F μ b X) +
         (labelledPointEntropyMean K F μ (b + 1) Y - labelledPointEntropyMean K F μ b Y)))
    (hfair : (labelledPointEntropyMean K F μ b X + labelledPointEntropyMean K F μ b Y) / 2 ≤
      labelledPointEntropyMean K F ν b V) :
    (1 + labelledPointFullEntropyMean K F μ Z / ((Fintype.card ι : ℝ) * L)) / 2 -
      C / (2 * (Fintype.card ι - b : ℕ) * L) ≤
        labelledPointEntropyMean K F ν b V / ((b : ℝ) * L) := by
  have hx := labelledSubsetEntropy_forward_increment_le K μ
    (fun i r ω => F i r (X ω)) (fun _ _ => measurable_of_finite _) b hb hbq
  have hy := labelledSubsetEntropy_forward_increment_le K μ
    (fun i r ω => F i r (Y ω)) (fun _ _ => measurable_of_finite _) b hb hbq
  apply normalized_enrichment_of_budget b (Fintype.card ι) hb hbq L _ C
    (labelledPointEntropyMean K F μ b X) (labelledPointEntropyMean K F μ b Y)
    (labelledPointEntropyMean K F ν b V)
    (labelledPointEntropyMean K F μ (b + 1) X - labelledPointEntropyMean K F μ b X)
    (labelledPointEntropyMean K F μ (b + 1) Y - labelledPointEntropyMean K F μ b Y)
    hL (labelledPointFullEntropyMean_nonneg K F μ Z) _ hx hy hfair
  linarith

end BinaryFormMoat.GeometryIntegration

#print axioms BinaryFormMoat.EntropyIntegration.normalized_enrichment_of_budget
#print axioms BinaryFormMoat.EntropyIntegration.normalized_enrichment_iterate
#print axioms BinaryFormMoat.EntropyIntegration.normalized_enrichment_iterate_nonneg
#print axioms BinaryFormMoat.GeometryIntegration.labelledPoint_normalized_enrichment
