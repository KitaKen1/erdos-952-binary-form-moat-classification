import Integrations.SharedData435

namespace BinaryFormMoat.EntropyIntegration
open MeasureTheory ProbabilityTheory

private theorem hitIndicator_eq {Ω G : Type*} [DecidableEq G]
    (K : Finset G) (T : Ω → G) :
    (T ⁻¹' (K : Set G)).indicator (fun _ => (1 : ℝ)) =
      (fun ω => if T ω ∈ K then (1 : ℝ) else 0) := by
  classical
  funext ω
  simp [Set.indicator]

def empiricalHitCount {ι G : Type*} [Fintype ι] [DecidableEq G] [Add G]
    (K : Finset G) (x : G) (h : ι → G) : ℕ :=
  (Finset.univ.filter (fun j => x + h j ∈ K)).card

noncomputable def empiricalList {ι G : Type*} [Fintype ι] [Fintype G]
    [DecidableEq G] [Add G] (K : Finset G) (t : ℝ) (h : ι → G) : Finset G := by
  classical
  exact Finset.univ.filter (fun x => (empiricalHitCount K x h : ℝ) ≤ t)

theorem mem_empiricalList {ι G : Type*} [Fintype ι] [Fintype G]
    [DecidableEq G] [Add G] (K : Finset G) (t : ℝ) (h : ι → G) (x : G) :
    x ∈ empiricalList K t h ↔ (empiricalHitCount K x h : ℝ) ≤ t := by
  classical
  simp [empiricalList]

theorem empiricalHitCount_eq_sum {ι G : Type*} [Fintype ι] [DecidableEq G] [Add G]
    (K : Finset G) (x : G) (h : ι → G) :
    (empiricalHitCount K x h : ℝ) = ∑ j, if x + h j ∈ K then (1 : ℝ) else 0 := by
  classical
  simp [empiricalHitCount, ← Finset.sum_boole]

theorem measurable_empiricalHitCount {Ω ι G : Type*} [MeasurableSpace Ω]
    [Fintype ι] [Fintype G] [DecidableEq G] [Add G]
    [MeasurableSpace G] [MeasurableSingletonClass G]
    (K : Finset G) (Y : Ω → G) (D : Ω → (ι → G))
    (hY : Measurable Y) (hD : Measurable D) :
    Measurable (fun ω => (empiricalHitCount K (Y ω) (D ω) : ℝ)) := by
  classical
  simp only [empiricalHitCount_eq_sum]
  apply Finset.measurable_sum
  intro j _
  have hj := (measurable_of_finite (fun z : G × G => z.1 + z.2)).comp
    (hY.prodMk ((measurable_pi_apply j).comp hD))
  change Measurable (fun ω => Y ω + D ω j) at hj
  simpa only [hitIndicator_eq] using
    (measurable_const : Measurable (fun _ : Ω => (1 : ℝ))).indicator
      (hj K.finite_toSet.measurableSet)

theorem integral_empiricalHitCount {Ω ι G : Type*} [MeasurableSpace Ω]
    [Fintype ι] [DecidableEq G] [Add G] [MeasurableSpace G] [MeasurableSingletonClass G]
    (μ : Measure Ω) [IsFiniteMeasure μ] (K : Finset G)
    (Y : Ω → G) (D : Ω → (ι → G))
    (htrial : ∀ j, Measurable (fun ω => Y ω + D ω j)) :
    (∫ ω, (empiricalHitCount K (Y ω) (D ω) : ℝ) ∂μ) =
      ∑ j, μ.real {ω | Y ω + D ω j ∈ K} := by
  classical
  have hi : ∀ j, Integrable (fun ω => if Y ω + D ω j ∈ K then (1 : ℝ) else 0) μ := by
    intro j
    simpa only [hitIndicator_eq] using
      (integrable_const (1 : ℝ) : Integrable (fun _ : Ω => (1 : ℝ)) μ).indicator
        ((htrial j) K.finite_toSet.measurableSet)
  simp_rw [empiricalHitCount_eq_sum]
  rw [integral_finsetSum _ (fun j _ => hi j)]
  apply Finset.sum_congr rfl
  intro j _
  have h := integral_indicator_const (μ := μ) (1 : ℝ) ((htrial j) K.finite_toSet.measurableSet)
  rw [hitIndicator_eq] at h
  have he : (fun ω => Y ω + D ω j) ⁻¹' (K : Set G) =
      {ω | Y ω + D ω j ∈ K} := by ext; simp
  rw [he] at h
  simpa only [smul_eq_mul, mul_one] using h

/-- Only the one-trial marginal is used; trials may be dependent. -/
theorem integral_empiricalHitCount_of_common_law {Ω ι G : Type*} [MeasurableSpace Ω]
    [Fintype ι] [DecidableEq G] [Add G] [MeasurableSpace G] [MeasurableSingletonClass G]
    (μ : Measure Ω) [IsFiniteMeasure μ] (K : Finset G)
    (Y Z : Ω → G) (D : Ω → (ι → G))
    (htrial : ∀ j, Measurable (fun ω => Y ω + D ω j))
    (hlaw : ∀ j, IdentDistrib (fun ω => Y ω + D ω j) Z μ μ) :
    (∫ ω, (empiricalHitCount K (Y ω) (D ω) : ℝ) ∂μ) =
      (Fintype.card ι : ℝ) * μ.real (Z ⁻¹' (K : Set G)) := by
  classical
  rw [integral_empiricalHitCount μ K Y D htrial]
  have he : ∀ j, μ.real {ω | Y ω + D ω j ∈ K} = μ.real (Z ⁻¹' (K : Set G)) := by
    intro j
    exact congrArg ENNReal.toReal ((hlaw j).measure_mem_eq K.finite_toSet.measurableSet)
  simp_rw [he]
  simp

theorem rare_finset_mass_le {Ω G : Type*} [MeasurableSpace Ω]
    [DecidableEq G] [MeasurableSpace G] [MeasurableSingletonClass G]
    (μ : Measure Ω) [IsFiniteMeasure μ] (K : Finset G) (Z : Ω → G)
    (hZ : Measurable Z) (b : ℝ)
    (hrare : ∀ u ∈ K, μ.real (Z ⁻¹' {u}) ≤ b) :
    μ.real (Z ⁻¹' (K : Set G)) ≤ (K.card : ℝ) * b := by
  rw [← sum_measureReal_preimage_singleton K (fun u _ => hZ (MeasurableSet.singleton u))]
  calc
    _ ≤ ∑ u ∈ K, b := Finset.sum_le_sum hrare
    _ = _ := by simp

theorem true_empiricalList_success_of_mean {Ω ι G : Type*} [MeasurableSpace Ω]
    [Fintype ι] [Fintype G] [DecidableEq G] [Add G]
    [MeasurableSpace G] [MeasurableSingletonClass G]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (K : Finset G)
    (Y : Ω → G) (D : Ω → (ι → G)) (hY : Measurable Y) (hD : Measurable D)
    (t m : ℝ) (ht : 0 < t)
    (hmean : (∫ ω, (empiricalHitCount K (Y ω) (D ω) : ℝ) ∂μ) ≤ m) :
    1 - m / t ≤ μ.real {ω | Y ω ∈ empiricalList K t (D ω)} := by
  classical
  let f := fun ω => (empiricalHitCount K (Y ω) (D ω) : ℝ)
  have htrial : ∀ j, Measurable (fun ω => Y ω + D ω j) := fun j =>
    (measurable_of_finite (fun z : G × G => z.1 + z.2)).comp
      (hY.prodMk ((measurable_pi_apply j).comp hD))
  have hi : Integrable f μ := by
    simp only [f, empiricalHitCount_eq_sum]
    apply integrable_finsetSum
    intro j _
    simpa only [hitIndicator_eq] using
      (integrable_const (1 : ℝ) : Integrable (fun _ : Ω => (1 : ℝ)) μ).indicator
        ((htrial j) K.finite_toSet.measurableSet)
  have hmark := mul_meas_ge_le_integral_of_nonneg
    (ae_of_all μ (fun ω => Nat.cast_nonneg (empiricalHitCount K (Y ω) (D ω)))) hi t
  have hbad : μ.real {ω | t < f ω} ≤ m / t := by
    apply (le_div_iff₀ ht).mpr
    calc
      _ = t * μ.real {ω | t < f ω} := by ring
      _ ≤ t * μ.real {ω | t ≤ f ω} := mul_le_mul_of_nonneg_left
        (measureReal_mono (μ := μ) (show {ω | t < f ω} ⊆ {ω | t ≤ f ω} from
          fun ω h => by
            have h' : t < f ω := by simpa only [Set.mem_ofPred_eq] using h
            simpa only [Set.mem_ofPred_eq] using h'.le)) ht.le
      _ ≤ _ := hmark.trans hmean
  have hset : {ω | Y ω ∈ empiricalList K t (D ω)} = {ω | t < f ω}ᶜ := by
    ext ω
    simp [mem_empiricalList, f, not_lt]
  rw [hset, measureReal_compl]
  · simp only [probReal_univ]
    linarith
  · exact measurableSet_lt measurable_const (measurable_empiricalHitCount K Y D hY hD)

/-- The source's delta/(tau+delta) success bound, before any independence
or conditional-trial assumptions are introduced. -/
theorem true_empiricalList_success_of_common_law {Ω ι G : Type*} [MeasurableSpace Ω]
    [Fintype ι] [Fintype G] [DecidableEq G] [Add G]
    [MeasurableSpace G] [MeasurableSingletonClass G]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (K : Finset G)
    (Y Z : Ω → G) (D : Ω → (ι → G)) (hY : Measurable Y) (hD : Measurable D)
    (hlaw : ∀ j, IdentDistrib (fun ω => Y ω + D ω j) Z μ μ)
    (hn : 0 < Fintype.card ι) (hK : K.Nonempty) (τ δ : ℝ) (hτ : 0 ≤ τ) (hδ : 0 < δ)
    (hrare : μ.real (Z ⁻¹' (K : Set G)) ≤ τ * K.card / Fintype.card G) :
    δ / (τ + δ) ≤ μ.real {ω | Y ω ∈ empiricalList K
      ((Fintype.card ι : ℝ) * (τ + δ) * K.card / Fintype.card G) (D ω)} := by
  classical
  have hp : (0 : ℝ) < Fintype.card G := by
    rcases hK with ⟨x, _⟩
    exact_mod_cast (Fintype.card_pos_iff.mpr ⟨x⟩)
  have hk : (0 : ℝ) < K.card := by exact_mod_cast hK.card_pos
  have hn' : (0 : ℝ) < Fintype.card ι := by exact_mod_cast hn
  have htd : 0 < τ + δ := add_pos_of_nonneg_of_pos hτ hδ
  have htrial : ∀ j, Measurable (fun ω => Y ω + D ω j) := fun j =>
    (measurable_of_finite (fun z : G × G => z.1 + z.2)).comp
      (hY.prodMk ((measurable_pi_apply j).comp hD))
  have hmean : (∫ ω, (empiricalHitCount K (Y ω) (D ω) : ℝ) ∂μ) ≤
      (Fintype.card ι : ℝ) * τ * K.card / Fintype.card G := by
    rw [integral_empiricalHitCount_of_common_law μ K Y Z D htrial hlaw]
    convert mul_le_mul_of_nonneg_left hrare hn'.le using 1; ring
  have h := true_empiricalList_success_of_mean μ K Y D hY hD _ _
    (div_pos (mul_pos (mul_pos hn' htd) hk) hp) hmean
  convert h using 1
  field_simp [ne_of_gt hn', ne_of_gt hk, ne_of_gt hp, ne_of_gt htd]
  ring

theorem true_empiricalList_success_ge_delta {Ω ι G : Type*} [MeasurableSpace Ω]
    [Fintype ι] [Fintype G] [DecidableEq G] [Add G]
    [MeasurableSpace G] [MeasurableSingletonClass G]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (K : Finset G)
    (Y Z : Ω → G) (D : Ω → (ι → G))
    (hY : Measurable Y) (hZ : Measurable Z) (hD : Measurable D)
    (hlaw : ∀ j, IdentDistrib (fun ω => Y ω + D ω j) Z μ μ)
    (hn : 0 < Fintype.card ι) (hK : K.Nonempty) (τ δ : ℝ)
    (hτ : 0 ≤ τ) (hδ : 0 < δ) (hsmall : τ + δ ≤ 1)
    (hrare : ∀ u ∈ K, μ.real (Z ⁻¹' {u}) ≤ τ / Fintype.card G) :
    δ ≤ μ.real {ω | Y ω ∈ empiricalList K
      ((Fintype.card ι : ℝ) * (τ + δ) * K.card / Fintype.card G) (D ω)} := by
  have hm := rare_finset_mass_le μ K Z hZ _ hrare
  have hm' : μ.real (Z ⁻¹' (K : Set G)) ≤ τ * K.card / Fintype.card G := by
    convert hm using 1; ring
  have h := true_empiricalList_success_of_common_law μ K Y Z D hY hD hlaw
    hn hK τ δ hτ hδ hm'
  apply le_trans _ h
  apply (le_div_iff₀ (add_pos_of_nonneg_of_pos hτ hδ)).mpr
  nlinarith

theorem success_with_small_list {Ω S T : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsFiniteMeasure μ] (X : Ω → S) (Z : Ω → T)
    (L : T → Finset S) (M : ℕ) :
    μ.real {ω | X ω ∈ L (Z ω)} - μ.real {ω | M < (L (Z ω)).card} ≤
      μ.real {ω | X ω ∈ L (Z ω) ∧ (L (Z ω)).card ≤ M} := by
  classical
  have hsub : {ω | X ω ∈ L (Z ω)} ⊆
      {ω | X ω ∈ L (Z ω) ∧ (L (Z ω)).card ≤ M} ∪ {ω | M < (L (Z ω)).card} := by
    intro ω hω
    by_cases hs : (L (Z ω)).card ≤ M
    · exact Or.inl ⟨hω, hs⟩
    · exact Or.inr (lt_of_not_ge hs)
  have h := (measureReal_mono (μ := μ) hsub).trans (measureReal_union_le (μ := μ) _ _)
  linarith

end BinaryFormMoat.EntropyIntegration

#print axioms BinaryFormMoat.EntropyIntegration.mem_empiricalList
#print axioms BinaryFormMoat.EntropyIntegration.empiricalHitCount_eq_sum
#print axioms BinaryFormMoat.EntropyIntegration.measurable_empiricalHitCount
#print axioms BinaryFormMoat.EntropyIntegration.integral_empiricalHitCount
#print axioms BinaryFormMoat.EntropyIntegration.integral_empiricalHitCount_of_common_law
#print axioms BinaryFormMoat.EntropyIntegration.rare_finset_mass_le
#print axioms BinaryFormMoat.EntropyIntegration.true_empiricalList_success_of_mean
#print axioms BinaryFormMoat.EntropyIntegration.true_empiricalList_success_of_common_law
#print axioms BinaryFormMoat.EntropyIntegration.true_empiricalList_success_ge_delta
#print axioms BinaryFormMoat.EntropyIntegration.success_with_small_list
