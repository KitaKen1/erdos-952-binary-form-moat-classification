import Integrations.RareResidueEntropy435

noncomputable section
namespace BinaryFormMoat.EntropyIntegration
open MeasureTheory ProbabilityTheory

/-- A deficient coordinate pays p^(-beta)/8. The manuscript's Pinsker
argument only required a constant times p^(-2*beta). -/
theorem deficient_coordinate_entropy_deficit {Ω G : Type*} [MeasurableSpace Ω]
    [Fintype G] [Nonempty G] [MeasurableSpace G] [MeasurableSingletonClass G]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (Z : Ω → G) (hZ : Measurable Z)
    (τ β : ℝ) (hτ : τ ≤ 3 / 8)
    (hbad : (Fintype.card G : ℝ) ^ (1 - β) ≤ (lowProbabilityResidues μ Z τ).card) :
    (Fintype.card G : ℝ) ^ (-β) / 8 ≤ Real.log (Fintype.card G) - entropy Z μ := by
  have hn : (0 : ℝ) < Fintype.card G := by exact_mod_cast (Fintype.card_pos : 0 < Fintype.card G)
  have he : (Fintype.card G : ℝ) ^ (-β) / 8 =
      (Fintype.card G : ℝ) ^ (1 - β) / (8 * Fintype.card G) := by
    rw [Real.rpow_sub hn, Real.rpow_one, Real.rpow_neg hn.le]
    field_simp
  rw [he]
  exact (div_le_div_of_nonneg_right hbad (by positivity)).trans
    (lowProbabilityResidues_card_le_entropy_deficit μ Z hZ τ hτ)

/-- The constant observation has no entropy cost, including finite laws
with zero individual source masses. -/
theorem condEntropy_unit_const {Ω G : Type*} [MeasurableSpace Ω]
    [Fintype G] [MeasurableSpace G] [MeasurableSingletonClass G]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (Z : Ω → G) (hZ : Measurable Z) :
    condEntropy Z (fun _ : Ω => (() : Unit)) μ = entropy Z μ := by
  let : FiniteRange Z := ⟨Set.toFinite _⟩
  let : FiniteRange (fun _ : Ω => (() : Unit)) := ⟨Set.toFinite _⟩
  exact (indepFun_const (f := Z) (μ := μ) (() : Unit)).condEntropy_eq_entropy hZ
    (measurable_const : Measurable (fun _ : Ω => (() : Unit)))

/-- ANY high joint-entropy input bounds deficient coordinates. In particular
s=1 applies to the actual terminal singleton mean. Coordinate independence
is not required. The common upper alphabet N pays for varying primes. -/
theorem high_entropy_few_deficient_coordinates {Ω ι Q : Type*} [MeasurableSpace Ω]
    [Fintype ι] [DecidableEq ι] [Nonempty ι] [Fintype Q] [Nonempty Q]
    [MeasurableSpace Q] [MeasurableSingletonClass Q]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (K : ι × Q → Type*) [∀ c, Fintype (K c)] [∀ c, Nonempty (K c)]
    [∀ c, MeasurableSpace (K c)] [∀ c, MeasurableSingletonClass (K c)]
    (Z : ∀ c, Ω → K c) (hZ : ∀ c, Measurable (Z c))
    (s : ℕ) (hs : 1 ≤ s) (hsk : s ≤ Fintype.card ι)
    (ε τ β N : ℝ) (hτ : τ ≤ 3 / 8) (hβ : 0 ≤ β) (hN : 0 < N)
    (hcard : ∀ c, (Fintype.card (K c) : ℝ) ≤ N)
    (high : (1 - ε) * (s : ℝ) * coordinateLogMean K ≤ labelSubsetJointEntropy μ K Z s) :
    ((deficientCoordinates μ K Z τ β).card : ℝ) /
      (Fintype.card ι * (Fintype.card Q : ℝ)) ≤
        8 * ε * coordinateLogMean K * N ^ β := by
  classical
  let B := deficientCoordinates μ K Z τ β
  let a := N ^ (-β) / 8
  have ha : 0 < a := div_pos (Real.rpow_pos_of_pos hN _) (by norm_num)
  have hl : ∀ c ∈ B, a ≤ Real.log (Fintype.card (K c)) -
      condEntropy (Z c) (fun _ : Ω => (() : Unit)) μ := by
    intro c hc
    rw [condEntropy_unit_const μ (Z c) (hZ c)]
    have hn : (0 : ℝ) < Fintype.card (K c) := by
      exact_mod_cast (Fintype.card_pos : 0 < Fintype.card (K c))
    apply le_trans (div_le_div_of_nonneg_right
      (Real.rpow_le_rpow_of_nonpos hn (hcard c) (neg_nonpos.mpr hβ)) (by norm_num))
    exact deficient_coordinate_entropy_deficit μ (Z c) (hZ c) τ β hτ
      ((mem_deficientCoordinates μ K Z τ β c).mp hc)
  have h := shared_data_few_high_deficit_coordinates μ K Z (fun _ : Ω => (() : Unit)) hZ
    measurable_const s hs hsk ε 0 high (by simp) B a ha hl
  have he : ((ε + 0) * coordinateLogMean K) / a =
      8 * ε * coordinateLogMean K * N ^ β := by
    dsimp only [a]
    rw [Real.rpow_neg hN.le]
    field_simp
    ring
  exact h.trans_eq he

end BinaryFormMoat.EntropyIntegration
#print axioms BinaryFormMoat.EntropyIntegration.deficient_coordinate_entropy_deficit
#print axioms BinaryFormMoat.EntropyIntegration.condEntropy_unit_const
#print axioms BinaryFormMoat.EntropyIntegration.high_entropy_few_deficient_coordinates
