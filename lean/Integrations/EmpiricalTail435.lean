import Integrations.BernoulliLowerTail435
import Integrations.EmpiricalLists435
import Integrations.TranslationOverlap435

namespace BinaryFormMoat.EntropyIntegration
open MeasureTheory ProbabilityTheory

def hitTrialEvent {Ω ι G : Type*} [Add G]
    (K : Finset G) (x : G) (D : Ω → (ι → G)) (j : ι) : Set Ω :=
  {ω | x + D ω j ∈ K}

theorem measurableSet_hitTrialEvent {Ω ι G : Type*} [MeasurableSpace Ω]
    [Fintype G] [Add G] [MeasurableSpace G] [MeasurableSingletonClass G]
    (K : Finset G) (x : G) (D : Ω → (ι → G)) (hD : Measurable D) (j : ι) :
    MeasurableSet (hitTrialEvent K x D j) := by
  have hj := (measurable_of_finite (fun h : G => x + h)).comp
    ((measurable_pi_apply j).comp hD)
  exact hj K.finite_toSet.measurableSet

theorem independent_hit_trialIndicators {Ω ι G : Type*} [MeasurableSpace Ω]
    [Fintype G] [Add G] [MeasurableSpace G] [MeasurableSingletonClass G]
    (μ : Measure Ω) (K : Finset G) (x : G) (D : Ω → (ι → G))
    (hI : iIndepFun (fun j ω => D ω j) μ) :
    iIndepFun (fun j => trialIndicator (hitTrialEvent K x D j)) μ := by
  classical
  let g : G → ℝ := trialIndicator {h | x + h ∈ K}
  have h := hI.comp (fun _ => g) (fun _ => measurable_of_finite g)
  have he : (fun j => g ∘ (fun ω => D ω j)) =
      (fun j => trialIndicator (hitTrialEvent K x D j)) := by
    funext j ω
    by_cases hh : x + D ω j ∈ K <;> simp [g, trialIndicator, hitTrialEvent, Set.indicator, hh]
  rw [he] at h
  exact h

theorem trialCount_hits_eq_empiricalHitCount {Ω ι G : Type*} [Fintype ι]
    [DecidableEq G] [Add G] (K : Finset G) (x : G) (D : Ω → (ι → G)) (ω : Ω) :
    trialCount (hitTrialEvent K x D) Finset.univ ω = (empiricalHitCount K x (D ω) : ℝ) := by
  classical
  rw [empiricalHitCount_eq_sum]
  unfold trialCount
  apply Finset.sum_congr rfl
  intro j _
  by_cases hh : x + D ω j ∈ K <;> simp [trialIndicator, hitTrialEvent, Set.indicator, hh]

/-- Apply the independent-indicator tail to the existing empirical list
under the exact supplied law, including a conditional law if appropriate. -/
theorem empiricalList_candidate_lower_tail {Ω ι G : Type*} [MeasurableSpace Ω]
    [Fintype ι] [Fintype G] [DecidableEq G] [Add G]
    [MeasurableSpace G] [MeasurableSingletonClass G]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (K : Finset G) (x : G)
    (D : Ω → (ι → G)) (hD : Measurable D) (hI : iIndepFun (fun j ω => D ω j) μ)
    (q v : ℝ) (hq : 0 ≤ q) (hv : 0 ≤ v)
    (hfloor : ∀ j, q ≤ μ.real (hitTrialEvent K x D j)) :
    μ.real {ω | x ∈ empiricalList K ((Fintype.card ι : ℝ) * (1 - v) * q) (D ω)} ≤
      Real.exp (-(Fintype.card ι : ℝ) * q * v ^ 2 / 2) := by
  have h := measure_trialCount_lower_tail μ (hitTrialEvent K x D) Finset.univ
    (measurableSet_hitTrialEvent K x D hD) (independent_hit_trialIndicators μ K x D hI)
    q v hq hv (fun j _ => hfloor j)
  simp only [Finset.card_univ] at h
  have he : {ω | x ∈ empiricalList K ((Fintype.card ι : ℝ) * (1 - v) * q) (D ω)} =
      {ω | trialCount (hitTrialEvent K x D) Finset.univ ω ≤ (1 - v) * (Fintype.card ι : ℝ) * q} := by
    ext ω
    simp only [Set.mem_ofPred_eq, mem_empiricalList, trialCount_hits_eq_empiricalHitCount]
    rw [mul_comm (Fintype.card ι : ℝ) (1 - v)]
  rw [he]
  exact h

/-- The source threshold n*(tau+delta)*r is below the hit floor
(tau+2*delta)*r. Retain the multiplicative n*r scale and factor 1/2. -/
theorem empiricalList_candidate_coverage_tail {Ω ι G : Type*} [MeasurableSpace Ω]
    [Fintype ι] [Fintype G] [DecidableEq G] [Add G]
    [MeasurableSpace G] [MeasurableSingletonClass G]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (K : Finset G) (x : G)
    (D : Ω → (ι → G)) (hD : Measurable D) (hI : iIndepFun (fun j ω => D ω j) μ)
    (τ δ r : ℝ) (hτ : 0 ≤ τ) (hδ : 0 < δ) (hr : 0 ≤ r) (hsmall : τ + 2 * δ ≤ 1)
    (hfloor : ∀ j, (τ + 2 * δ) * r ≤ μ.real (hitTrialEvent K x D j)) :
    μ.real {ω | x ∈ empiricalList K ((Fintype.card ι : ℝ) * (τ + δ) * r) (D ω)} ≤
      Real.exp (-δ ^ 2 * (Fintype.card ι : ℝ) * r / 2) := by
  have hc : 0 < τ + 2 * δ := by positivity
  have h := empiricalList_candidate_lower_tail μ K x D hD hI
    ((τ + 2 * δ) * r) (δ / (τ + 2 * δ)) (mul_nonneg hc.le hr)
    (div_nonneg hδ.le hc.le) hfloor
  have he : (Fintype.card ι : ℝ) * (1 - δ / (τ + 2 * δ)) * ((τ + 2 * δ) * r) =
      (Fintype.card ι : ℝ) * (τ + δ) * r := by
    field_simp [ne_of_gt hc]
    ring
  rw [he] at h
  apply h.trans
  apply Real.exp_le_exp.mpr
  have he' : -(Fintype.card ι : ℝ) * ((τ + 2 * δ) * r) * (δ / (τ + 2 * δ)) ^ 2 / 2 =
      (-δ ^ 2 * (Fintype.card ι : ℝ) * r / 2) / (τ + 2 * δ) := by
    field_simp [ne_of_gt hc]
  rw [he']
  apply (div_le_iff₀ hc).mpr
  have hn : -δ ^ 2 * (Fintype.card ι : ℝ) * r / 2 ≤ 0 :=
    div_nonpos_of_nonpos_of_nonneg
      (mul_nonpos_of_nonpos_of_nonneg
        (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (sq_nonneg δ)) (Nat.cast_nonneg _)) hr)
      (by norm_num)
  have hh := mul_le_mul_of_nonpos_left hsmall hn
  simpa only [mul_one] using hh

/-- A union bound over all candidates outside a deterministic exceptional
set. This does not assert that conditional trial independence is automatic. -/
theorem empiricalList_size_failure_le_of_candidate_tails {Ω ι G : Type*}
    [MeasurableSpace Ω] [Fintype ι] [Fintype G] [DecidableEq G] [Add G]
    (μ : Measure Ω) [IsFiniteMeasure μ] (K B : Finset G) (t : ℝ)
    (D : Ω → (ι → G)) (M : ℕ) (hB : B.card ≤ M) (b : ℝ) (hb : 0 ≤ b)
    (htail : ∀ x ∉ B, μ.real {ω | x ∈ empiricalList K t (D ω)} ≤ b) :
    μ.real {ω | M < (empiricalList K t (D ω)).card} ≤ (Fintype.card G : ℝ) * b := by
  classical
  let f := fun x : G => {ω | x ∈ empiricalList K t (D ω) ∧ x ∉ B}
  have hs : {ω | M < (empiricalList K t (D ω)).card} ⊆ ⋃ x, f x := by
    intro ω hω
    have hbig : M < (empiricalList K t (D ω)).card := by
      simpa only [Set.mem_ofPred_eq] using hω
    have hn : ¬ empiricalList K t (D ω) ⊆ B := by
      intro hsub
      have hc := Finset.card_le_card hsub
      omega
    rcases Finset.not_subset.mp hn with ⟨x, hx, hxB⟩
    exact Set.mem_iUnion.mpr ⟨x, by simpa only [f, Set.mem_ofPred_eq] using And.intro hx hxB⟩
  calc
    _ ≤ μ.real (⋃ x, f x) := measureReal_mono (μ := μ) hs
    _ ≤ ∑ x, μ.real (f x) := measureReal_iUnion_fintype_le f
    _ ≤ ∑ x : G, b := by
      apply Finset.sum_le_sum
      intro x _
      by_cases hx : x ∈ B
      · have he : f x = ∅ := by ext ω; simp [f, hx]
        rw [he]
        simpa using hb
      · apply le_trans _ (htail x hx)
        apply measureReal_mono (μ := μ)
        intro ω hω
        simp only [f, Set.mem_ofPred_eq] at hω ⊢
        exact hω.1
    _ = _ := by simp

theorem empiricalList_size_failure_le_of_hit_floors {Ω ι G : Type*} [MeasurableSpace Ω]
    [Fintype ι] [Fintype G] [DecidableEq G] [Add G]
    [MeasurableSpace G] [MeasurableSingletonClass G]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (K B : Finset G)
    (D : Ω → (ι → G)) (hD : Measurable D) (hI : iIndepFun (fun j ω => D ω j) μ)
    (M : ℕ) (hB : B.card ≤ M) (τ δ r : ℝ) (hτ : 0 ≤ τ) (hδ : 0 < δ)
    (hr : 0 ≤ r) (hsmall : τ + 2 * δ ≤ 1)
    (hfloor : ∀ x ∉ B, ∀ j, (τ + 2 * δ) * r ≤ μ.real (hitTrialEvent K x D j)) :
    μ.real {ω | M < (empiricalList K ((Fintype.card ι : ℝ) * (τ + δ) * r) (D ω)).card} ≤
      (Fintype.card G : ℝ) * Real.exp (-δ ^ 2 * (Fintype.card ι : ℝ) * r / 2) := by
  apply empiricalList_size_failure_le_of_candidate_tails μ K B _ D M hB _ (Real.exp_pos _).le
  intro x hx
  exact empiricalList_candidate_coverage_tail μ K x D hD hI τ δ r hτ hδ hr hsmall (hfloor x hx)

theorem empiricalList_size_failure_le_coverage_scale {Ω ι G : Type*} [MeasurableSpace Ω]
    [Fintype ι] [Fintype G] [DecidableEq G] [Add G]
    [MeasurableSpace G] [MeasurableSingletonClass G]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (K B : Finset G)
    (D : Ω → (ι → G)) (hD : Measurable D) (hI : iIndepFun (fun j ω => D ω j) μ)
    (M : ℕ) (hB : B.card ≤ M) (τ δ r β : ℝ) (hτ : 0 ≤ τ) (hδ : 0 < δ)
    (hr : 0 ≤ r) (hsmall : τ + 2 * δ ≤ 1)
    (hfloor : ∀ x ∉ B, ∀ j, (τ + 2 * δ) * r ≤ μ.real (hitTrialEvent K x D j))
    (hscale : (Fintype.card G : ℝ) ^ (-β) ≤ r) :
    μ.real {ω | M < (empiricalList K ((Fintype.card ι : ℝ) * (τ + δ) * r) (D ω)).card} ≤
      (Fintype.card G : ℝ) *
        Real.exp (-δ ^ 2 * (Fintype.card ι : ℝ) * (Fintype.card G : ℝ) ^ (-β) / 2) := by
  apply (empiricalList_size_failure_le_of_hit_floors μ K B D hD hI M hB τ δ r
    hτ hδ hr hsmall hfloor).trans
  apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
  apply Real.exp_le_exp.mpr
  have hc : -δ ^ 2 * (Fintype.card ι : ℝ) / 2 ≤ 0 :=
    div_nonpos_of_nonpos_of_nonneg
      (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (sq_nonneg δ)) (Nat.cast_nonneg _))
      (by norm_num)
  have h := mul_le_mul_of_nonpos_left hscale hc
  convert h using 1 <;> ring

theorem hitTrialEvent_probability_eq_weighted_sum {Ω ι G : Type*} [MeasurableSpace Ω]
    [Fintype G] [DecidableEq G] [Add G] [MeasurableSpace G] [MeasurableSingletonClass G]
    (μ : Measure Ω) [IsFiniteMeasure μ] (K : Finset G) (x : G)
    (D : Ω → (ι → G)) (hD : Measurable D) (j : ι) :
    μ.real (hitTrialEvent K x D j) =
      ∑ h : G, if x + h ∈ K then μ.real ((fun ω => D ω j) ⁻¹' {h}) else 0 := by
  classical
  let H : Finset G := Finset.univ.filter (fun h => x + h ∈ K)
  have he : hitTrialEvent K x D j = (fun ω => D ω j) ⁻¹' (H : Set G) := by
    ext ω
    simp [hitTrialEvent, H]
  rw [he, ← sum_measureReal_preimage_singleton (μ := μ) (f := fun ω => D ω j) H
    (fun h _ => ((measurable_pi_apply j).comp hD) (MeasurableSet.singleton h))]
  exact Finset.sum_filter _ _

/-- Coverage floors for the actual trial law, outside E, pass through the
translation-overlap estimate to a candidate's actual hit probability. -/
theorem hitTrialEvent_probability_floor_of_overlap {Ω ι G : Type*} [MeasurableSpace Ω]
    [Fintype G] [DecidableEq G] [AddGroup G] [MeasurableSpace G] [MeasurableSingletonClass G]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (K E : Finset G) (x : G)
    (D : Ω → (ι → G)) (hD : Measurable D) (j : ι) (α δ : ℝ) (hα : 0 ≤ α)
    (hfloor : ∀ h ∉ E, α ≤ μ.real ((fun ω => D ω j) ⁻¹' {h}))
    (hoverlap : (translationOverlap K E x : ℝ) ≤ δ * K.card) :
    α * (1 - δ) * K.card ≤ μ.real (hitTrialEvent K x D j) := by
  rw [hitTrialEvent_probability_eq_weighted_sum μ K x D hD j]
  exact translated_hit_probability_lower_of_overlap K E x
    (fun h => μ.real ((fun ω => D ω j) ⁻¹' {h})) α δ hα
    (fun _ => measureReal_nonneg) hfloor hoverlap

/-- Fixed-law coverage-to-small-list estimate. The law can be the exact
A=a conditional law, but constructing that law and its independence is separate. -/
theorem empiricalList_size_failure_le_of_coverage {Ω ι G : Type*} [MeasurableSpace Ω]
    [Fintype ι] [Fintype G] [DecidableEq G] [AddGroup G]
    [MeasurableSpace G] [MeasurableSingletonClass G]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (K E : Finset G) (hK : K.Nonempty)
    (D : Ω → (ι → G)) (hD : Measurable D) (hI : iIndepFun (fun j ω => D ω j) μ)
    (M : ℕ) (τ τ' δ : ℝ) (hτ : 0 ≤ τ) (hτ' : 0 ≤ τ') (hδ : 0 < δ)
    (hsmall : τ + 2 * δ ≤ 1) (hgap : τ + 2 * δ ≤ τ' * (1 - δ))
    (hsize : (E.card : ℝ) / δ ≤ M)
    (hcoverage : ∀ j, ∀ h ∉ E, τ' / Fintype.card G ≤ μ.real ((fun ω => D ω j) ⁻¹' {h})) :
    μ.real {ω | M < (empiricalList K
      ((Fintype.card ι : ℝ) * (τ + δ) * ((K.card : ℝ) / Fintype.card G)) (D ω)).card} ≤
      (Fintype.card G : ℝ) * Real.exp
        (-δ ^ 2 * (Fintype.card ι : ℝ) * ((K.card : ℝ) / Fintype.card G) / 2) := by
  classical
  let B := overlapExceptionalCandidates K E δ
  have hB : B.card ≤ M := by
    exact_mod_cast (overlapExceptionalCandidates_card_le K E hK δ hδ).trans hsize
  apply empiricalList_size_failure_le_of_hit_floors μ K B D hD hI M hB τ δ
    ((K.card : ℝ) / Fintype.card G) hτ hδ (div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)) hsmall
  intro x hx j
  have h := hitTrialEvent_probability_floor_of_overlap μ K E x D hD j
    (τ' / Fintype.card G) δ (div_nonneg hτ' (Nat.cast_nonneg _)) (hcoverage j)
    (overlap_le_of_not_exceptional K E δ x hx)
  have hg := mul_le_mul_of_nonneg_right hgap
    (div_nonneg (Nat.cast_nonneg K.card) (Nat.cast_nonneg (Fintype.card G)))
  apply le_trans hg
  convert h using 1
  ring

end BinaryFormMoat.EntropyIntegration

#print axioms BinaryFormMoat.EntropyIntegration.measurableSet_hitTrialEvent
#print axioms BinaryFormMoat.EntropyIntegration.independent_hit_trialIndicators
#print axioms BinaryFormMoat.EntropyIntegration.trialCount_hits_eq_empiricalHitCount
#print axioms BinaryFormMoat.EntropyIntegration.empiricalList_candidate_lower_tail
#print axioms BinaryFormMoat.EntropyIntegration.empiricalList_candidate_coverage_tail
#print axioms BinaryFormMoat.EntropyIntegration.empiricalList_size_failure_le_of_candidate_tails
#print axioms BinaryFormMoat.EntropyIntegration.empiricalList_size_failure_le_of_hit_floors
#print axioms BinaryFormMoat.EntropyIntegration.empiricalList_size_failure_le_coverage_scale
#print axioms BinaryFormMoat.EntropyIntegration.hitTrialEvent_probability_eq_weighted_sum
#print axioms BinaryFormMoat.EntropyIntegration.hitTrialEvent_probability_floor_of_overlap
#print axioms BinaryFormMoat.EntropyIntegration.empiricalList_size_failure_le_of_coverage
