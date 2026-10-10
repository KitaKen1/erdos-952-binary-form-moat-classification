import Integrations.PFRInformation435

namespace BinaryFormMoat.EntropyIntegration
open MeasureTheory ProbabilityTheory

/-- Subadditivity for finite tuples with different coordinate alphabets. -/
theorem entropy_finTuple_le_sum {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsZeroOrProbabilityMeasure μ] (n : ℕ) (K : Fin n → Type*)
    [∀ i, MeasurableSpace (K i)] [∀ i, MeasurableSingletonClass (K i)]
    [∀ i, Fintype (K i)] (X : ∀ i, Ω → K i) (hX : ∀ i, Measurable (X i)) :
    entropy (fun ω i => X i ω) μ ≤ ∑ i, entropy (X i) μ := by
  induction n with
  | zero =>
    have he : (fun ω i => X i ω) = (fun _ : Ω => (fun i : Fin 0 => Fin.elim0 i)) := by
      funext ω i
      exact Fin.elim0 i
    simp [he]
  | succ n ih =>
    let Y := fun ω (i : Fin n) => X i.succ ω
    have hY : Measurable Y := Measurable.of_eval (fun i => hX i.succ)
    have he : entropy (fun ω i => X i ω) μ =
        entropy (fun ω => (X 0 ω, Y ω)) μ := by
      let e := Fin.consEquiv K
      have h := entropy_comp_of_injective μ ((hX 0).prodMk hY) e e.injective
      have hf : (fun ω i => X i ω) = e ∘ (fun ω => (X 0 ω, Y ω)) := by
        funext ω i
        cases i using Fin.cases <;> rfl
      simpa only [hf] using h
    rw [he, Fin.sum_univ_succ]
    exact (entropy_pair_le_add (hX 0) hY μ).trans
      (add_le_add (le_refl _) (ih (fun i => K i.succ) (fun i => X i.succ) (fun i => hX i.succ)))

theorem entropy_pi_le_sum {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι]
    (μ : Measure Ω) [IsZeroOrProbabilityMeasure μ] (K : ι → Type*)
    [∀ i, MeasurableSpace (K i)] [∀ i, MeasurableSingletonClass (K i)]
    [∀ i, Fintype (K i)] (X : ∀ i, Ω → K i) (hX : ∀ i, Measurable (X i)) :
    entropy (fun ω i => X i ω) μ ≤ ∑ i, entropy (X i) μ := by
  classical
  let e := Fintype.equivFin ι
  let f := Equiv.piCongrLeft' K e
  have he := entropy_comp_of_injective μ (Measurable.of_eval hX) f f.injective
  have h := entropy_finTuple_le_sum μ (Fintype.card ι) (fun j => K (e.symm j))
    (fun j => X (e.symm j)) (fun j => hX (e.symm j))
  change entropy (f ∘ (fun ω i => X i ω)) μ ≤ _ at h
  rw [he] at h
  simpa only [e.symm.sum_comp (fun i => entropy (X i) μ)] using h

/-- Conditional subadditivity is proved fiber by fiber, including zero fibers. -/
theorem condEntropy_pi_le_sum {Ω ι T : Type*} [MeasurableSpace Ω] [Fintype ι]
    [MeasurableSpace T] [MeasurableSingletonClass T] [Fintype T]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (K : ι → Type*)
    [∀ i, MeasurableSpace (K i)] [∀ i, MeasurableSingletonClass (K i)]
    [∀ i, Fintype (K i)] (X : ∀ i, Ω → K i) (Z : Ω → T)
    (hX : ∀ i, Measurable (X i)) (hZ : Measurable Z) :
    condEntropy (fun ω i => X i ω) Z μ ≤ ∑ i, condEntropy (X i) Z μ := by
  classical
  simp_rw [condEntropy_eq_sum_fintype _ _ _ hZ]
  rw [Finset.sum_comm]
  apply Finset.sum_le_sum
  intro z _
  rw [← Finset.mul_sum]
  exact mul_le_mul_of_nonneg_left (entropy_pi_le_sum (μ[|Z ← z]) K X hX)
    measureReal_nonneg

theorem entropy_pi_sub_shared_le_condEntropy_sum {Ω ι T : Type*}
    [MeasurableSpace Ω] [Fintype ι]
    [MeasurableSpace T] [MeasurableSingletonClass T] [Fintype T]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (K : ι → Type*)
    [∀ i, MeasurableSpace (K i)] [∀ i, MeasurableSingletonClass (K i)]
    [∀ i, Fintype (K i)] (X : ∀ i, Ω → K i) (Z : Ω → T)
    (hX : ∀ i, Measurable (X i)) (hZ : Measurable Z) :
    entropy (fun ω i => X i ω) μ - entropy Z μ ≤ ∑ i, condEntropy (X i) Z μ := by
  classical
  exact (condEntropy_ge_entropy_sub_observation_entropy μ _ Z (Measurable.of_eval hX) hZ).trans
    (condEntropy_pi_le_sum μ K X Z hX hZ)

theorem conditional_coordinate_deficit_nonneg {Ω S T : Type*}
    [MeasurableSpace Ω] [MeasurableSpace S] [MeasurableSingletonClass S] [Fintype S]
    [MeasurableSpace T] [MeasurableSingletonClass T]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (X : Ω → S) (Z : Ω → T) :
    0 ≤ Real.log (Fintype.card S) - condEntropy X Z μ := by
  exact sub_nonneg.mpr (condEntropy_le_log_card X Z μ)

end BinaryFormMoat.EntropyIntegration

#print axioms BinaryFormMoat.EntropyIntegration.entropy_finTuple_le_sum
#print axioms BinaryFormMoat.EntropyIntegration.entropy_pi_le_sum
#print axioms BinaryFormMoat.EntropyIntegration.condEntropy_pi_le_sum
#print axioms BinaryFormMoat.EntropyIntegration.entropy_pi_sub_shared_le_condEntropy_sum
#print axioms BinaryFormMoat.EntropyIntegration.conditional_coordinate_deficit_nonneg
