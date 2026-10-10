import Integrations.CoordinateEntropy435
import Integrations.OriginalContinuation435

namespace BinaryFormMoat.EntropyIntegration
open MeasureTheory ProbabilityTheory

/-- The upstream finite independent-entropy theorem with an explicit law. -/
theorem entropy_fin_eq_sum_of_iIndepFun {Ω H : Type*} [MeasurableSpace Ω]
    [Fintype H] [MeasurableSpace H] [MeasurableSingletonClass H]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (n : ℕ) (D : Fin n → Ω → H)
    (hD : ∀ j, Measurable (D j)) (hI : iIndepFun D μ) :
    entropy (fun ω j => D j ω) μ = ∑ j, entropy (D j) μ := by
  let : MeasureSpace Ω := ⟨μ⟩
  exact iIndepFun.entropy_eq_add hD hI

theorem entropy_pi_eq_sum_of_iIndepFun {Ω H J : Type*} [MeasurableSpace Ω]
    [Fintype H] [MeasurableSpace H] [MeasurableSingletonClass H] [Fintype J]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (D : J → Ω → H)
    (hD : ∀ j, Measurable (D j)) (hI : iIndepFun D μ) :
    entropy (fun ω j => D j ω) μ = ∑ j, entropy (D j) μ := by
  classical
  let e := Fintype.equivFin J
  let f := Equiv.piCongrLeft' (fun _ : J => H) e
  have he := entropy_comp_of_injective μ (Measurable.of_eval hD) f f.injective
  have hi : iIndepFun (fun j : Fin (Fintype.card J) => D (e.symm j)) μ :=
    hI.precomp e.symm.injective
  have h := entropy_fin_eq_sum_of_iIndepFun μ (Fintype.card J)
    (fun j => D (e.symm j)) (fun j => hD (e.symm j)) hi
  change entropy (f ∘ (fun ω j => D j ω)) μ = _ at h
  rw [he] at h
  simpa only [e.symm.sum_comp (fun j => entropy (D j) μ)] using h

/-- Positive fibers use actual independence; zero fibers have zero weight. -/
theorem condEntropy_pi_eq_sum_of_fiber_independence {Ω H J A : Type*}
    [MeasurableSpace Ω] [Fintype H] [MeasurableSpace H] [MeasurableSingletonClass H]
    [Fintype J] [Fintype A] [MeasurableSpace A] [MeasurableSingletonClass A]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (D : J → Ω → H) (V : Ω → A)
    (hD : ∀ j, Measurable (D j)) (hV : Measurable V)
    (hI : ∀ a, μ (V ⁻¹' {a}) ≠ 0 → iIndepFun D (μ[|V ⁻¹' {a}])) :
    condEntropy (fun ω j => D j ω) V μ = ∑ j, condEntropy (D j) V μ := by
  classical
  simp_rw [condEntropy_eq_sum_fintype _ _ _ hV]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _
  rw [← Finset.mul_sum]
  by_cases ha : μ (V ⁻¹' {a}) = 0
  · simp [measureReal_def, ha]
  · have : IsProbabilityMeasure (μ[|V ⁻¹' {a}]) := cond_isProbabilityMeasure ha
    rw [entropy_pi_eq_sum_of_iIndepFun _ D hD (hI a ha)]

/-- Package information is subadditive when packages are independent
conditional on exactly the pair (X,O), not merely on a finer checkpoint. -/
theorem condMutualInfo_pi_le_sum_of_fiber_independence {Ω H J C U : Type*}
    [MeasurableSpace Ω] [Fintype H] [MeasurableSpace H] [MeasurableSingletonClass H]
    [Fintype J] [Fintype C] [MeasurableSpace C] [MeasurableSingletonClass C]
    [Fintype U] [MeasurableSpace U] [MeasurableSingletonClass U]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (X : Ω → C) (O : Ω → U)
    (D : J → Ω → H) (hX : Measurable X) (hO : Measurable O)
    (hD : ∀ j, Measurable (D j))
    (hI : ∀ a : C × U, μ ((fun ω => (X ω, O ω)) ⁻¹' {a}) ≠ 0 →
      iIndepFun D (μ[|(fun ω => (X ω, O ω)) ⁻¹' {a}])) :
    condMutualInfo X (fun ω j => D j ω) O μ ≤ ∑ j, condMutualInfo X (D j) O μ := by
  classical
  have he := condEntropy_pi_eq_sum_of_fiber_independence μ D
    (fun ω => (X ω, O ω)) hD (hX.prodMk hO) hI
  have hu := condEntropy_pi_le_sum μ (fun _ : J => H) D O hD hO
  rw [condMutualInfo_comm hX (Measurable.of_eval hD),
    condMutualInfo_eq' (Measurable.of_eval hD) hX hO, he]
  simp_rw [condMutualInfo_comm hX (hD _), condMutualInfo_eq' (hD _) hX hO]
  rw [Finset.sum_sub_distrib]
  linarith

end BinaryFormMoat.EntropyIntegration

#print axioms BinaryFormMoat.EntropyIntegration.entropy_fin_eq_sum_of_iIndepFun
#print axioms BinaryFormMoat.EntropyIntegration.entropy_pi_eq_sum_of_iIndepFun
#print axioms BinaryFormMoat.EntropyIntegration.condEntropy_pi_eq_sum_of_fiber_independence
#print axioms BinaryFormMoat.EntropyIntegration.condMutualInfo_pi_le_sum_of_fiber_independence
