import Integrations.ConditionalAverage435
import Integrations.CoverageRounding435

namespace BinaryFormMoat.EntropyIntegration
open MeasureTheory ProbabilityTheory

theorem mean_smallListSuccess_ge_of_fiber_coverage {Ω A C T : Type*}
    [MeasurableSpace Ω] [Fintype A] [MeasurableSpace A] [MeasurableSingletonClass A]
    [Fintype C] [DecidableEq C] [MeasurableSpace T] [MeasurableSingletonClass T] [Fintype T]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (V : Ω → A) (hV : Measurable V)
    (K : C → Type*) (X : ∀ c, Ω → K c) (H : Ω → T) (hH : Measurable H)
    (B : Finset C) (hB : B.Nonempty) (L : ∀ c, T → Finset (K c)) (M : C → ℕ)
    (good : A → Finset C) (δ η η' : ℝ) (hδ : 0 ≤ δ)
    (htrue : ∀ c ∈ B, δ ≤ μ.real {ω | X c ω ∈ L c (H ω)})
    (hgood : ∀ a, μ (V ⁻¹' {a}) ≠ 0 → ∀ c ∈ good a,
      fiberConditionalReal μ V a {ω | M c < (L c (H ω)).card} ≤ δ / 100)
    (hbad : ∀ a, μ (V ⁻¹' {a}) ≠ 0 →
      ((Finset.univ \ good a).card : ℝ) ≤ η' * Fintype.card C)
    (hθ : η ≤ (B.card : ℝ) / Fintype.card C) (hbudget : η' ≤ η * δ / 100) :
    δ / 2 ≤ finiteRealMean B (fun c => smallListSuccess μ (X c) H (L c) (M c)) := by
  have hE : ∀ c, MeasurableSet {ω | M c < (L c (H ω)).card} := by
    intro c
    exact (measurable_of_finite (fun t : T => (L c t).card)).comp hH
      measurableSet_Ioi
  have h := mean_probability_le_coverage_budget μ V hV B hB good _ hE
    δ η η' hδ hgood hbad hθ hbudget
  apply mean_smallListSuccess_ge_of_list_failure μ K X H B hB L M δ htrue
  linarith only [h, hδ]

section Shared
variable {Ω A ι R T : Type*} [MeasurableSpace Ω]
  [Fintype A] [MeasurableSpace A] [MeasurableSingletonClass A]
  [Fintype ι] [DecidableEq ι] [Fintype R] [DecidableEq R] [Nonempty R]
  [MeasurableSpace R] [MeasurableSingletonClass R]
  [MeasurableSpace T] [MeasurableSingletonClass T] [Fintype T]
  [MeasurableSpace Bool] [MeasurableSingletonClass Bool]
  (μ : Measure Ω) [IsProbabilityMeasure μ] (V : Ω → A) (hV : Measurable V)
  (K : ι × R → Type*)
  [∀ c, MeasurableSpace (K c)] [∀ c, MeasurableSingletonClass (K c)] [∀ c, Fintype (K c)]
  (X : ∀ c, Ω → K c) (H : Ω → T) (hX : ∀ c, Measurable (X c)) (hH : Measurable H)
include hV hX hH

/-- The success floor is now derived from exact conditional failures and
bad-coordinate counts. Walk joint entropy and the shared data bound remain inputs. -/
theorem shared_data_few_small_list_coordinates_of_fiber_coverage
    (s : ℕ) (hs : 1 ≤ s) (hsk : s ≤ Fintype.card ι) (ε κ : ℝ)
    (hjoint : (1 - ε) * (s : ℝ) * coordinateLogMean K ≤ labelSubsetJointEntropy μ K X s)
    (hdata : entropy H μ ≤ κ * (s : ℝ) * coordinateLogMean K)
    (B : Finset (ι × R)) (hB : B.Nonempty)
    (L : ∀ c, T → Finset (K c)) (M : ι × R → ℕ) (hM : ∀ c ∈ B, 1 ≤ M c)
    (good : A → Finset (ι × R)) (δ β logT η η' : ℝ)
    (hδ : 0 < δ) (hβ : 0 < β) (hT : 0 < logT)
    (htrue : ∀ c ∈ B, δ ≤ μ.real {ω | X c ω ∈ L c (H ω)})
    (hgood : ∀ a, μ (V ⁻¹' {a}) ≠ 0 → ∀ c ∈ good a,
      fiberConditionalReal μ V a {ω | M c < (L c (H ω)).card} ≤ δ / 100)
    (hbad : ∀ a, μ (V ⁻¹' {a}) ≠ 0 →
      ((Finset.univ \ good a).card : ℝ) ≤ η' * Fintype.card (ι × R))
    (hmix : η' ≤ η * δ / 100)
    (hgap : ∀ c ∈ B, β / 2 * logT ≤
      Real.log (Fintype.card (K c)) - Real.log (M c : ℝ))
    (hlog : Real.log (Real.exp 1 / (δ / 2)) ≤ β / 4 * logT)
    (hscale : coordinateLogMean K ≤ 2 * logT)
    (hcost : 0 ≤ ε + κ) (hbudget : ε + κ ≤ η * δ * β / 16) :
    (B.card : ℝ) / (Fintype.card ι * (Fintype.card R : ℝ)) ≤ η := by
  by_cases hθ : (B.card : ℝ) / (Fintype.card ι * (Fintype.card R : ℝ)) ≤ η
  · exact hθ
  · have hθ' : η ≤ (B.card : ℝ) / Fintype.card (ι × R) := by
      simpa only [Fintype.card_prod, Nat.cast_mul] using (lt_of_not_ge hθ).le
    have hmean := mean_smallListSuccess_ge_of_fiber_coverage μ V hV K X H hH
      B hB L M good δ η η' hδ.le htrue hgood hbad hθ' hmix
    exact shared_data_few_small_list_coordinates μ K X H hX hH s hs hsk ε κ
      hjoint hdata B hB L M hM δ β logT η hδ hβ hT hmean hgap hlog hscale hcost hbudget

end Shared

section Empirical
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

/-- End-to-end empirical-list certificate for the one-step transfer.
All conditional statements use the actual fiber law of the same experiment.
The original common trial marginal and conditional independence are explicit
premises. This does not construct the walk experiment or its entropy inputs. -/
theorem shared_data_few_empirical_list_coordinates
    (s : ℕ) (hs : 1 ≤ s) (hsk : s ≤ Fintype.card ι) (ε κ : ℝ)
    (hjoint : (1 - ε) * (s : ℝ) * coordinateLogMean G ≤ labelSubsetJointEntropy μ G Y s)
    (hdata : entropy H μ ≤ κ * (s : ℝ) * coordinateLogMean G)
    (B : Finset (ι × R)) (hB : B.Nonempty) (K : ∀ c, Finset (G c))
    (good : A → Finset (ι × R)) (E : ∀ (_a : A) c, Finset (G c))
    (τ δ β β' logT η η' : ℝ) (hτ : 0 ≤ τ) (hτmax : τ ≤ 3 / 8)
    (hδ : 0 < δ) (hδmax : δ ≤ 1 / 64) (hβ' : 0 < β') (hβ'max : β' ≤ 2)
    (hT : 0 < logT) (hn : 0 < Fintype.card J)
    (hKsize : ∀ c, (K c).card = rareSampleSize (Fintype.card (G c)) β)
    (hrare : ∀ c ∈ B, ∀ u ∈ K c, μ.real (Z c ⁻¹' {u}) ≤ τ / Fintype.card (G c))
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
    (hp : ∀ c ∈ B, logT ≤ Real.log (Fintype.card (G c)))
    (hlog : Real.log (Real.exp 1 / (δ / 2)) ≤ β' / 4 * logT)
    (hscale : coordinateLogMean G ≤ 2 * logT)
    (hcost : 0 ≤ ε + κ) (hbudget : ε + κ ≤ η * δ * β' / 16) :
    (B.card : ℝ) / (Fintype.card ι * (Fintype.card R : ℝ)) ≤ η := by
  classical
  let L := fun c t => empiricalList (K c)
    ((Fintype.card J : ℝ) * (τ + δ) * ((K c).card : ℝ) / Fintype.card (G c)) (D c t)
  let M := fun c => smallListCutoff (Fintype.card (G c)) β'
  have hD : ∀ c, Measurable (fun ω => D c (H ω)) := fun c =>
    (measurable_of_finite (D c)).comp hH
  have hK : ∀ c, (K c).Nonempty := fun c => Finset.card_pos.mp
    (by rw [hKsize]; exact rareSampleSize_pos _ Fintype.card_pos β)
  apply shared_data_few_small_list_coordinates_of_fiber_coverage μ V hV G Y H hY hH
    s hs hsk ε κ hjoint hdata B hB L M
    (fun c _ => smallListCutoff_pos _ (Nat.one_le_iff_ne_zero.mpr Fintype.card_ne_zero) β' hβ'max)
    good δ β' logT η η' hδ hβ' hT
  · intro c hc
    exact true_empiricalList_success_ge_delta μ (K c) (Y c) (Z c) _
      (hY c) (hZ c) (hD c) (hlaw c) hn (hK c) τ δ hτ hδ
      (by linarith) (hrare c hc)
  · intro a ha c hc
    have := cond_isProbabilityMeasure (μ := μ) ha
    have h := empiricalList_size_failure_le_rounded_coverage (μ[|V ⁻¹' {a}])
      (K c) (E a c) (hK c) _ (hD c) (hI a ha c hc) τ β β' δ hτ hτmax hδ hδmax
      (hsize a ha c hc) (hmargin c) (hKsize c) (hcoverage a ha c hc)
    simpa only [fiberConditionalReal, L, M, mul_div_assoc] using h.trans (htail c)
  · exact hbad
  · exact hmix
  · intro c hc
    exact (mul_le_mul_of_nonneg_left (hp c hc) (by positivity : 0 ≤ β' / 2)).trans
      (smallListCutoff_log_gap _ (Nat.one_le_iff_ne_zero.mpr Fintype.card_ne_zero) β' hβ'max)
  · exact hlog
  · exact hscale
  · exact hcost
  · exact hbudget

end Empirical
end BinaryFormMoat.EntropyIntegration

#print axioms BinaryFormMoat.EntropyIntegration.mean_smallListSuccess_ge_of_fiber_coverage
#print axioms BinaryFormMoat.EntropyIntegration.shared_data_few_small_list_coordinates_of_fiber_coverage
#print axioms BinaryFormMoat.EntropyIntegration.shared_data_few_empirical_list_coordinates
