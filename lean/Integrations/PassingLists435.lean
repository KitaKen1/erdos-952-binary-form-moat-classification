import Integrations.OriginalContinuation435
import Mathlib.Analysis.SpecialFunctions.Exp

namespace BinaryFormMoat.EntropyIntegration
open MeasureTheory ProbabilityTheory

/-- Candidates rejected by none of the independently sampled packages. -/
noncomputable def passingList {C H J : Type*} [Fintype C] [Fintype J]
    (reject : C → H → Prop) (h : J → H) : Finset C := by
  classical
  exact Finset.univ.filter (fun x => ∀ j, ¬ reject x (h j))

theorem mem_passingList {C H J : Type*} [Fintype C] [Fintype J]
    (reject : C → H → Prop) (h : J → H) (x : C) :
    x ∈ passingList reject h ↔ ∀ j, ¬ reject x (h j) := by
  classical
  simp [passingList]

theorem passingList_card_eq_sum {C H J : Type*} [Fintype C] [DecidableEq C] [Fintype J]
    (reject : C → H → Prop) (h : J → H) :
    ((passingList reject h).card : ℝ) = ∑ x : C, if x ∈ passingList reject h then 1 else 0 := by
  classical
  simp

theorem integral_passingList_card {Ω C H J : Type*} [Fintype Ω] [MeasurableSpace Ω]
    [MeasurableSingletonClass Ω] [Fintype C] [Fintype J]
    (μ : Measure Ω) [IsFiniteMeasure μ] (reject : C → H → Prop) (D : Ω → (J → H)) :
    (∫ ω, ((passingList reject (D ω)).card : ℝ) ∂μ) =
      ∑ x : C, μ.real {ω | x ∈ passingList reject (D ω)} := by
  classical
  simp_rw [passingList_card_eq_sum]
  rw [integral_finsetSum _ (fun _ _ => Integrable.of_finite)]
  apply Finset.sum_congr rfl
  intro x _
  have he : (fun ω => if x ∈ passingList reject (D ω) then (1 : ℝ) else 0) =
      {ω | x ∈ passingList reject (D ω)}.indicator 1 := by
    funext ω
    simp [Set.indicator_apply]
  rw [he, integral_indicator_one (Set.toFinite _).measurableSet]

section IndependentPackages
variable {C H J : Type*} [Fintype C] [Fintype H] [Fintype J]
  [MeasurableSpace H] [MeasurableSingletonClass H]
  (ν : Measure H) [IsProbabilityMeasure ν] (reject : C → H → Prop)

omit [Fintype H] [MeasurableSingletonClass H] in
/-- The exact product construction supplies the survival law, including no packages. -/
theorem passingList_survival_probability (x : C) :
    (Measure.pi (fun _ : J => ν)).real {h | x ∈ passingList reject h} =
      (ν.real {h | ¬ reject x h}) ^ Fintype.card J := by
  classical
  have he : {h : J → H | x ∈ passingList reject h} =
      Set.univ.pi (fun _ : J => {h : H | ¬ reject x h}) := by
    ext h
    simp [mem_passingList]
  simp only [he, measureReal_def, Measure.pi_pi, Finset.prod_const,
    Finset.card_univ, ENNReal.toReal_pow]

theorem passingList_survival_exp_bound (x : C) (ε : ℝ)
    (hε : ε ≤ ν.real {h | reject x h}) :
    (Measure.pi (fun _ : J => ν)).real {h | x ∈ passingList reject h} ≤
      Real.exp (-(Fintype.card J : ℝ) * ε) := by
  rw [passingList_survival_probability]
  have hc : ν.real {h | ¬ reject x h} = 1 - ν.real {h | reject x h} := by
    rw [show {h | ¬ reject x h} = ({h | reject x h} : Set H)ᶜ from rfl,
      measureReal_compl (Set.toFinite _).measurableSet, probReal_univ]
  have he : ν.real {h | ¬ reject x h} ≤ Real.exp (-ε) := by
    rw [hc]
    have h := Real.add_one_le_exp (-ε)
    linarith
  have hp := pow_le_pow_left₀ (measureReal_nonneg (μ := ν) (s := {h | ¬ reject x h}))
    he (Fintype.card J)
  rw [← Real.exp_nat_mul] at hp
  convert hp using 1
  congr 1
  ring

/-- Few exceptional candidates plus exponentially few ordinary survivors. -/
theorem expected_passingList_card_le (B : Finset C) (ε : ℝ)
    (hfloor : ∀ x ∉ B, ε ≤ ν.real {h | reject x h}) :
    (∫ h : J → H, ((passingList reject h).card : ℝ) ∂Measure.pi (fun _ : J => ν)) ≤
      (B.card : ℝ) + Fintype.card C * Real.exp (-(Fintype.card J : ℝ) * ε) := by
  classical
  rw [integral_passingList_card]
  calc
    _ ≤ ∑ x : C, ((if x ∈ B then (1 : ℝ) else 0) +
        Real.exp (-(Fintype.card J : ℝ) * ε)) := by
      apply Finset.sum_le_sum
      intro x _
      by_cases hx : x ∈ B
      · rw [ite_eq_left hx]
        exact measureReal_le_one.trans (le_add_of_nonneg_right (Real.exp_nonneg _))
      · rw [ite_eq_right hx, zero_add]
        exact passingList_survival_exp_bound (J := J) ν reject x ε (hfloor x hx)
    _ = _ := by
      simp [Finset.sum_add_distrib]

theorem expected_passingList_card_le_of_quota (B : Finset C) (ε b t : ℝ)
    (hfloor : ∀ x ∉ B, ε ≤ ν.real {h | reject x h}) (hB : (B.card : ℝ) ≤ b)
    (ht : Fintype.card C * Real.exp (-(Fintype.card J : ℝ) * ε) ≤ t) :
    (∫ h : J → H, ((passingList reject h).card : ℝ) ∂Measure.pi (fun _ : J => ν)) ≤ b + t := by
  exact (expected_passingList_card_le ν reject B ε hfloor).trans (add_le_add hB ht)

/-- The source's 4A exceptional candidates and A survivor quota give 5A. -/
theorem expected_passingList_card_source_bound (B : Finset C) (ε A : ℝ)
    (hfloor : ∀ x ∉ B, ε ≤ ν.real {h | reject x h}) (hB : (B.card : ℝ) ≤ 4 * A)
    (ht : Fintype.card C * Real.exp (-(Fintype.card J : ℝ) * ε) ≤ A) :
    (∫ h : J → H, ((passingList reject h).card : ℝ) ∂Measure.pi (fun _ : J => ν)) ≤ 5 * A := by
  have h := expected_passingList_card_le_of_quota ν reject B ε (4 * A) A hfloor hB ht
  linarith

end IndependentPackages
end BinaryFormMoat.EntropyIntegration

#print axioms BinaryFormMoat.EntropyIntegration.mem_passingList
#print axioms BinaryFormMoat.EntropyIntegration.passingList_card_eq_sum
#print axioms BinaryFormMoat.EntropyIntegration.integral_passingList_card
#print axioms BinaryFormMoat.EntropyIntegration.passingList_survival_probability
#print axioms BinaryFormMoat.EntropyIntegration.passingList_survival_exp_bound
#print axioms BinaryFormMoat.EntropyIntegration.expected_passingList_card_le
#print axioms BinaryFormMoat.EntropyIntegration.expected_passingList_card_le_of_quota
#print axioms BinaryFormMoat.EntropyIntegration.expected_passingList_card_source_bound
