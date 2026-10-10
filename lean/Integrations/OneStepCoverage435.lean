import Integrations.CoverageTransfer435

namespace BinaryFormMoat.EntropyIntegration
open MeasureTheory ProbabilityTheory

noncomputable def lowProbabilityResidues {Ω G : Type*} [MeasurableSpace Ω] [Fintype G]
    (μ : Measure Ω) (Z : Ω → G) (τ : ℝ) : Finset G := by
  classical
  exact Finset.univ.filter (fun u => μ.real (Z ⁻¹' {u}) < τ / Fintype.card G)

theorem mem_lowProbabilityResidues {Ω G : Type*} [MeasurableSpace Ω] [Fintype G]
    (μ : Measure Ω) (Z : Ω → G) (τ : ℝ) (u : G) :
    u ∈ lowProbabilityResidues μ Z τ ↔ μ.real (Z ⁻¹' {u}) < τ / Fintype.card G := by
  classical
  simp [lowProbabilityResidues]

noncomputable def deficientCoordinates {Ω C : Type*} [MeasurableSpace Ω] [Fintype C]
    (μ : Measure Ω) (G : C → Type*) [∀ c, Fintype (G c)] (Z : ∀ c, Ω → G c)
    (τ β : ℝ) : Finset C := by
  classical
  exact Finset.univ.filter (fun c => (Fintype.card (G c) : ℝ) ^ (1 - β) ≤
    (lowProbabilityResidues μ (Z c) τ).card)

theorem mem_deficientCoordinates {Ω C : Type*} [MeasurableSpace Ω] [Fintype C]
    (μ : Measure Ω) (G : C → Type*) [∀ c, Fintype (G c)] (Z : ∀ c, Ω → G c)
    (τ β : ℝ) (c : C) :
    c ∈ deficientCoordinates μ G Z τ β ↔ (Fintype.card (G c) : ℝ) ^ (1 - β) ≤
      (lowProbabilityResidues μ (Z c) τ).card := by
  classical
  simp [deficientCoordinates]

/-- Choose the prescribed ceiling-size rare sets on deficient coordinates,
and arbitrary sets of the same size elsewhere. No extra loss in the cutoff. -/
theorem exists_coverage_witness_sets {Ω C : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (G : C → Type*) [∀ c, Fintype (G c)] [∀ c, Nonempty (G c)]
    (Z : ∀ c, Ω → G c) (τ β : ℝ) (hβ : 0 ≤ β) (B : Finset C)
    (hB : ∀ c ∈ B, (Fintype.card (G c) : ℝ) ^ (1 - β) ≤
      (lowProbabilityResidues μ (Z c) τ).card) :
    ∃ K : ∀ c, Finset (G c),
      (∀ c, (K c).card = rareSampleSize (Fintype.card (G c)) β) ∧
      (∀ c ∈ B, ∀ u ∈ K c, μ.real (Z c ⁻¹' {u}) ≤ τ / Fintype.card (G c)) := by
  classical
  have hex : ∀ c, ∃ K : Finset (G c),
      K.card = rareSampleSize (Fintype.card (G c)) β ∧
      (c ∈ B → K ⊆ lowProbabilityResidues μ (Z c) τ) := by
    intro c
    by_cases hc : c ∈ B
    · obtain ⟨K, hsub, hcard⟩ := exists_rare_sample (lowProbabilityResidues μ (Z c) τ)
        β (hB c hc)
      exact ⟨K, hcard, fun _ => hsub⟩
    · obtain ⟨K, _, hcard⟩ := Finset.exists_subset_card_eq
        (show rareSampleSize (Fintype.card (G c)) β ≤ (Finset.univ : Finset (G c)).card by
          simpa using rareSampleSize_le _ (Nat.one_le_iff_ne_zero.mpr Fintype.card_ne_zero) β hβ)
      exact ⟨K, hcard, fun h => (hc h).elim⟩
  choose K hK using hex
  refine ⟨K, fun c => (hK c).1, ?_⟩
  intro c hc u hu
  exact ((mem_lowProbabilityResidues μ (Z c) τ u).mp ((hK c).2 hc hu)).le

section Transfer
variable {Ω A ι R T J : Type*} [MeasurableSpace Ω]
  [Fintype A] [MeasurableSpace A] [MeasurableSingletonClass A]
  [Fintype ι] [DecidableEq ι] [Fintype R] [DecidableEq R] [Nonempty R]
  [MeasurableSpace R] [MeasurableSingletonClass R]
  [MeasurableSpace T] [MeasurableSingletonClass T] [Fintype T] [Fintype J]
  [MeasurableSpace Bool] [MeasurableSingletonClass Bool]
  (μ : Measure Ω) [IsProbabilityMeasure μ] (V : Ω → A) (hV : Measurable V)
  (G : ι × R → Type*)
  [∀ c, MeasurableSpace (G c)] [∀ c, MeasurableSingletonClass (G c)] [∀ c, Fintype (G c)]
  [∀ c, DecidableEq (G c)] [∀ c, AddGroup (G c)]
  (Y Z : ∀ c, Ω → G c) (H : Ω → T)
  (hY : ∀ c, Measurable (Y c)) (hZ : ∀ c, Measurable (Z c)) (hH : Measurable H)
  (D : ∀ c, T → J → G c)
include hV hY hZ hH

/-- Coverage transfer from actual conditional displacement probability floors.
The final deficient set is defined from the terminal law, not supplied as an
arbitrary set. The same experiment supplies all marginals, fibers and entropy.
Constructing its walk realization and the entropy budgets remains separate. -/
theorem one_step_coverage_transfer
    (s : ℕ) (hs : 1 ≤ s) (hsk : s ≤ Fintype.card ι) (ε κ : ℝ)
    (hjoint : (1 - ε) * (s : ℝ) * coordinateLogMean G ≤ labelSubsetJointEntropy μ G Y s)
    (hdata : entropy H μ ≤ κ * (s : ℝ) * coordinateLogMean G)
    (good : A → Finset (ι × R)) (E : ∀ (_a : A) c, Finset (G c))
    (τ δ β β' logT η η' : ℝ) (hτ : 0 ≤ τ) (hτmax : τ ≤ 3 / 8)
    (hδ : 0 < δ) (hδmax : δ ≤ 1 / 64) (hβ : 0 ≤ β)
    (hβ' : 0 < β') (hβ'max : β' ≤ 2) (hT : 0 < logT) (hη : 0 ≤ η)
    (hn : 0 < Fintype.card J)
    (hlaw : ∀ c j, IdentDistrib (fun ω => Y c ω + D c (H ω) j) (Z c) μ μ)
    (hI : ∀ a, μ (V ⁻¹' {a}) ≠ 0 → ∀ c ∈ good a,
      iIndepFun (fun j ω => D c (H ω) j) (μ[|V ⁻¹' {a}]))
    (hcoverage : ∀ a, μ (V ⁻¹' {a}) ≠ 0 → ∀ c ∈ good a, ∀ j, ∀ u ∉ E a c,
      (τ + 4 * δ) / Fintype.card (G c) ≤
        fiberConditionalReal μ V a ((fun ω => D c (H ω) j) ⁻¹' {u}))
    (hsize : ∀ a, μ (V ⁻¹' {a}) ≠ 0 → ∀ c ∈ good a,
      ((E a c).card : ℝ) < (Fintype.card (G c) : ℝ) ^ (1 - β'))
    (hbad : ∀ a, μ (V ⁻¹' {a}) ≠ 0 →
      ((Finset.univ \ good a).card : ℝ) ≤ η' * Fintype.card (ι × R))
    (hmix : η' ≤ η * δ / 100)
    (hmargin : ∀ c, δ⁻¹ < (Fintype.card (G c) : ℝ) ^ (β' / 2))
    (htail : ∀ c, (Fintype.card (G c) : ℝ) *
      Real.exp (-δ ^ 2 * (Fintype.card J : ℝ) * (Fintype.card (G c) : ℝ) ^ (-β) / 2) ≤ δ / 100)
    (hp : ∀ c, logT ≤ Real.log (Fintype.card (G c)))
    (hlog : Real.log (Real.exp 1 / (δ / 2)) ≤ β' / 4 * logT)
    (hscale : coordinateLogMean G ≤ 2 * logT)
    (hcost : 0 ≤ ε + κ) (hbudget : ε + κ ≤ η * δ * β' / 16) :
    ((deficientCoordinates μ G Z τ β).card : ℝ) /
      (Fintype.card ι * (Fintype.card R : ℝ)) ≤ η := by
  classical
  let B := deficientCoordinates μ G Z τ β
  by_cases hB : B.Nonempty
  · obtain ⟨K, hKsize, hrare⟩ := exists_coverage_witness_sets μ G Z τ β hβ B
      (fun c hc => (mem_deficientCoordinates μ G Z τ β c).mp hc)
    exact shared_data_few_empirical_list_coordinates μ V hV G Y Z H hY hZ hH D
      s hs hsk ε κ hjoint hdata B hB K good E τ δ β β' logT η η'
      hτ hτmax hδ hδmax hβ' hβ'max hT hn hKsize hrare hlaw hI hcoverage hsize
      hbad hmix hmargin htail (fun c _ => hp c) hlog hscale hcost hbudget
  · have he : B = ∅ := Finset.not_nonempty_iff_eq_empty.mp hB
    change (B.card : ℝ) / _ ≤ η
    simpa [he] using hη

end Transfer
end BinaryFormMoat.EntropyIntegration

#print axioms BinaryFormMoat.EntropyIntegration.mem_lowProbabilityResidues
#print axioms BinaryFormMoat.EntropyIntegration.mem_deficientCoordinates
#print axioms BinaryFormMoat.EntropyIntegration.exists_coverage_witness_sets
#print axioms BinaryFormMoat.EntropyIntegration.one_step_coverage_transfer
