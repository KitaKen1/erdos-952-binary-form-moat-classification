import Integrations.FiniteCheckpoint435
import Integrations.PassingLoss435

namespace BinaryFormMoat.EntropyIntegration
open MeasureTheory ProbabilityTheory

/-- Compress AFTER conditioning on exactly the recorded checkpoint data.
The positive branch is the pushforward of the ORIGINAL conditional source. -/
theorem finiteCheckpointLaw_originalContinuation_map
    {Ω A H : Type*} [Fintype Ω] [Fintype A] [Fintype H]
    [MeasurableSpace Ω] [MeasurableSingletonClass Ω]
    [MeasurableSpace A] [MeasurableSingletonClass A]
    [MeasurableSpace H] [MeasurableSingletonClass H]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (V : Ω → A) (W : Ω → H)
    (h₀ : H) (a : A) (ha : μ (V ⁻¹' {a}) ≠ 0) :
    originalContinuationLaw (finiteCheckpointLaw μ V W) h₀ a =
      (μ[|V ⁻¹' {a}]).map W := by
  have ha' : finiteCheckpointLaw μ V W (Prod.fst ⁻¹' {a}) ≠ 0 := by
    rwa [finiteCheckpointLaw_fiber]
  rw [originalContinuationLaw, ite_eq_right ha', finiteCheckpointLaw_cond,
    Measure.map_map measurable_snd (measurable_of_finite _)]
  rfl

/-- Candidate rejection probabilities are preserved by actual compression. -/
theorem finiteCheckpointLaw_originalContinuation_real
    {Ω A H : Type*} [Fintype Ω] [Fintype A] [Fintype H]
    [MeasurableSpace Ω] [MeasurableSingletonClass Ω]
    [MeasurableSpace A] [MeasurableSingletonClass A]
    [MeasurableSpace H] [MeasurableSingletonClass H]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (V : Ω → A) (W : Ω → H)
    (h₀ : H) (a : A) (ha : μ (V ⁻¹' {a}) ≠ 0) (E : Set H) :
    (originalContinuationLaw (finiteCheckpointLaw μ V W) h₀ a).real E =
      (μ[|V ⁻¹' {a}]).real (W ⁻¹' E) := by
  rw [finiteCheckpointLaw_originalContinuation_map μ V W h₀ a ha,
    map_measureReal_apply (measurable_of_finite _) (Set.toFinite _).measurableSet]

/-- An almost-sure ORIGINAL one-package truth survives all constructed
posterior packages. Only marginal preservation is needed for this step. -/
theorem originalResamplingLaw_true_in_passingList
    {A H J C : Type*} [Fintype A] [Fintype H] [Fintype J] [Fintype C]
    [MeasurableSpace A] [MeasurableSingletonClass A]
    [MeasurableSpace H] [MeasurableSingletonClass H]
    (θ : Measure (A × H)) [IsProbabilityMeasure θ] (h₀ : H)
    (X : A → C) (reject : C → H → Prop)
    (htrue : ∀ᵐ ω ∂θ, ¬ reject (X ω.1) ω.2) :
    ∀ᵐ ω ∂originalResamplingLaw (J := J) θ h₀,
      X ω.1 ∈ passingList reject ω.2 := by
  have hj (j : J) : ∀ᵐ ω ∂originalResamplingLaw (J := J) θ h₀,
      ¬ reject (X ω.1) (ω.2 j) :=
    (originalResamplingLaw_identDistrib θ h₀ id j).symm.ae_snd
      (p := fun ah : A × H => ¬ reject (X ah.1) ah.2)
      (Set.toFinite _).measurableSet htrue
  filter_upwards [ae_all_iff.mpr hj] with ω hω
  exact (mem_passingList _ _ _).mpr hω

/-- Exact checkpoint recording makes the true-value support automatic after
compression and resampling; it is not a new independence assumption. -/
theorem finiteCheckpointLaw_true_in_passingList
    {Ω A H J C : Type*} [Fintype Ω] [Fintype A] [Fintype H] [Fintype J] [Fintype C]
    [MeasurableSpace Ω] [MeasurableSingletonClass Ω]
    [MeasurableSpace A] [MeasurableSingletonClass A]
    [MeasurableSpace H] [MeasurableSingletonClass H]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (V : Ω → A) (W : Ω → H)
    (h₀ : H) (X : A → C) (reject : C → H → Prop)
    (htrue : ∀ᵐ ω ∂μ, ¬ reject (X (V ω)) (W ω)) :
    ∀ᵐ ω ∂originalResamplingLaw (J := J) (finiteCheckpointLaw μ V W) h₀,
      X ω.1 ∈ passingList reject ω.2 := by
  apply originalResamplingLaw_true_in_passingList _ h₀ X reject
  exact (finiteCheckpointLaw_identDistrib μ V W id).symm.ae_snd
    (p := fun ah : A × H => ¬ reject (X ah.1) ah.2)
    (Set.toFinite _).measurableSet htrue

end BinaryFormMoat.EntropyIntegration
#print axioms BinaryFormMoat.EntropyIntegration.finiteCheckpointLaw_originalContinuation_map
#print axioms BinaryFormMoat.EntropyIntegration.finiteCheckpointLaw_originalContinuation_real
#print axioms BinaryFormMoat.EntropyIntegration.originalResamplingLaw_true_in_passingList
#print axioms BinaryFormMoat.EntropyIntegration.finiteCheckpointLaw_true_in_passingList
