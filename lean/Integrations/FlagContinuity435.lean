import Integrations.SuccessEntropy435

namespace BinaryFormMoat.EntropyIntegration
open MeasureTheory ProbabilityTheory

theorem successEntropyCost_one_sub (a : ℝ) :
    successEntropyCost (1 - a) = successEntropyCost a := by
  unfold successEntropyCost
  rw [show 1 - (1 - a) = a by ring, add_comm]

section Flag
variable {Ω S T : Type*} [MeasurableSpace Ω]
  [MeasurableSpace S] [MeasurableSingletonClass S] [Fintype S]
  [MeasurableSpace T] [MeasurableSingletonClass T] [Fintype T]
  [MeasurableSpace Bool] [MeasurableSingletonClass Bool]
  (μ : Measure Ω) [IsProbabilityMeasure μ]
  (X : Ω → S) (Z : Ω → T) (E : Ω → Bool)

omit [IsProbabilityMeasure μ] [MeasurableSingletonClass T] [Fintype T] [MeasurableSpace Bool]
  [MeasurableSingletonClass Bool] in
/-- A zero-mass branch costs zero. Positive branches use their actual
conditional probability measure, with only the target alphabet charged. -/
theorem weighted_fiber_condEntropy_le (e : Bool) :
    μ.real (E ⁻¹' {e}) * condEntropy X Z (μ[|E ⁻¹' {e}]) ≤
      μ.real (E ⁻¹' {e}) * Real.log (Fintype.card S) := by
  by_cases he : μ.real (E ⁻¹' {e}) = 0
  · simp [he]
  · have := cond_isProbabilityMeasure_of_real he
    exact mul_le_mul_of_nonneg_left (condEntropy_le_log_card X Z _) measureReal_nonneg

/-- The good branch is a common lower bound; deleting the branch flag costs
its binary entropy, and the bad branch costs its mass times log |S|. -/
theorem condEntropy_flag_branch_bounds
    (hX : Measurable X) (hZ : Measurable Z) (hE : Measurable E) :
    μ.real (E ⁻¹' {false}) * condEntropy X Z (μ[|E ⁻¹' {false}]) ≤ condEntropy X Z μ ∧
    condEntropy X Z μ ≤
      μ.real (E ⁻¹' {false}) * condEntropy X Z (μ[|E ⁻¹' {false}]) +
      μ.real (E ⁻¹' {true}) * Real.log (Fintype.card S) +
      successEntropyCost (μ.real (E ⁻¹' {true})) := by
  have hswap := condEntropy_of_injective' μ hX (hZ.prodMk hE) Prod.swap
    Prod.swap_injective (hE.prodMk hZ)
  have hbranches := condEntropy_prod_eq_sum (X := X) μ hZ hE
  rw [Fintype.sum_bool] at hbranches
  change condEntropy X (fun ω => (E ω, Z ω)) μ =
    condEntropy X (fun ω => (Z ω, E ω)) μ at hswap
  have hlo := entropy_submodular μ hX hE hZ
  have hhi := condEntropy_le_flag_entropy μ X Z E hX hZ hE
  have hnonneg : 0 ≤ μ.real (E ⁻¹' {true}) * condEntropy X Z (μ[|E ⁻¹' {true}]) :=
    mul_nonneg measureReal_nonneg (condEntropy_nonneg _ _ _)
  have hbad := weighted_fiber_condEntropy_le μ X Z E true
  have hflag : entropy E μ = successEntropyCost (μ.real (E ⁻¹' {true})) := by
    rw [entropy_bool_eq_successEntropyCost μ E hE]
    have hm := bool_false_true_mass μ E hE
    have heq : μ.real (E ⁻¹' {false}) = 1 - μ.real (E ⁻¹' {true}) := by linarith
    rw [heq, successEntropyCost_one_sub]
  rw [hflag] at hhi
  constructor <;> linarith

omit [IsProbabilityMeasure μ] in
/-- Agreement on the good fiber gives equal branch conditional entropies,
including the zero fiber. The observations may differ on the bad fiber. -/
theorem condEntropy_flag_false_congr (X' : Ω → S) (Z' : Ω → T)
    (hX : Measurable X) (hZ : Measurable Z) (hX' : Measurable X') (hZ' : Measurable Z')
    (hE : Measurable E) (hgood : ∀ ω, E ω = false → X ω = X' ω ∧ Z ω = Z' ω) :
    condEntropy X Z (μ[|E ⁻¹' {false}]) = condEntropy X' Z' (μ[|E ⁻¹' {false}]) := by
  have ha := ae_cond_of_forall_mem (μ := μ) (hE (MeasurableSet.singleton false))
    (fun ω hω => hgood ω hω)
  rw [chain_rule'' _ hX hZ, chain_rule'' _ hX' hZ']
  have hp : entropy (fun ω => (X ω, Z ω)) (μ[|E ⁻¹' {false}]) =
      entropy (fun ω => (X' ω, Z' ω)) (μ[|E ⁻¹' {false}]) :=
    entropy_congr (ha.mono (fun _ h => Prod.ext h.1 h.2))
  have hz : entropy Z (μ[|E ⁻¹' {false}]) = entropy Z' (μ[|E ⁻¹' {false}]) :=
    entropy_congr (ha.mono (fun _ h => h.2))
  rw [hp, hz]

/-- Conditional entropy continuity from a concrete common-good coupling.
No logarithm of the side-observation alphabet occurs in the bound. -/
theorem condEntropy_flag_agreement_bound (X' : Ω → S) (Z' : Ω → T)
    (hX : Measurable X) (hZ : Measurable Z) (hX' : Measurable X') (hZ' : Measurable Z')
    (hE : Measurable E) (hgood : ∀ ω, E ω = false → X ω = X' ω ∧ Z ω = Z' ω) :
    |condEntropy X Z μ - condEntropy X' Z' μ| ≤
      successEntropyCost (μ.real (E ⁻¹' {true})) +
      μ.real (E ⁻¹' {true}) * Real.log (Fintype.card S) := by
  have h₀ := condEntropy_flag_branch_bounds μ X Z E hX hZ hE
  have h₁ := condEntropy_flag_branch_bounds μ X' Z' E hX' hZ' hE
  have he := condEntropy_flag_false_congr μ X Z E X' Z' hX hZ hX' hZ' hE hgood
  rw [he] at h₀
  rw [abs_le]
  constructor <;> linarith [h₀.1, h₀.2, h₁.1, h₁.2]

end Flag

/-- Two conditional-entropy comparisons charge the same target alphabet
for conditional mutual information, even when both side observations change. -/
theorem condMutualInfo_flag_agreement_bound {Ω S T U : Type*} [MeasurableSpace Ω]
    [MeasurableSpace S] [MeasurableSingletonClass S] [Fintype S]
    [MeasurableSpace T] [MeasurableSingletonClass T] [Fintype T]
    [MeasurableSpace U] [MeasurableSingletonClass U] [Fintype U]
    [MeasurableSpace Bool] [MeasurableSingletonClass Bool]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X X' : Ω → S) (Y Y' : Ω → T) (Z Z' : Ω → U) (E : Ω → Bool)
    (hX : Measurable X) (hX' : Measurable X') (hY : Measurable Y) (hY' : Measurable Y')
    (hZ : Measurable Z) (hZ' : Measurable Z') (hE : Measurable E)
    (hgood : ∀ ω, E ω = false → X ω = X' ω ∧ Y ω = Y' ω ∧ Z ω = Z' ω) :
    |condMutualInfo X Y Z μ - condMutualInfo X' Y' Z' μ| ≤
      2 * (successEntropyCost (μ.real (E ⁻¹' {true})) +
        μ.real (E ⁻¹' {true}) * Real.log (Fintype.card S)) := by
  have h₀ := condEntropy_flag_agreement_bound μ X Z E X' Z' hX hZ hX' hZ' hE
    (fun ω h => ⟨(hgood ω h).1, (hgood ω h).2.2⟩)
  have h₁ := condEntropy_flag_agreement_bound μ X (fun ω => (Y ω, Z ω)) E X'
    (fun ω => (Y' ω, Z' ω)) hX (hY.prodMk hZ) hX' (hY'.prodMk hZ') hE
    (fun ω h => ⟨(hgood ω h).1, Prod.ext (hgood ω h).2.1 (hgood ω h).2.2⟩)
  rw [condMutualInfo_eq' hX hY hZ μ, condMutualInfo_eq' hX' hY' hZ' μ, abs_le]
  have hb₀ := abs_le.mp h₀
  have hb₁ := abs_le.mp h₁
  constructor <;> linarith [hb₀.1, hb₀.2, hb₁.1, hb₁.2]

end BinaryFormMoat.EntropyIntegration

#print axioms BinaryFormMoat.EntropyIntegration.successEntropyCost_one_sub
#print axioms BinaryFormMoat.EntropyIntegration.weighted_fiber_condEntropy_le
#print axioms BinaryFormMoat.EntropyIntegration.condEntropy_flag_branch_bounds
#print axioms BinaryFormMoat.EntropyIntegration.condEntropy_flag_false_congr
#print axioms BinaryFormMoat.EntropyIntegration.condEntropy_flag_agreement_bound
#print axioms BinaryFormMoat.EntropyIntegration.condMutualInfo_flag_agreement_bound
