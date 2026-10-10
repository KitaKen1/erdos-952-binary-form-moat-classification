import Integrations.PosteriorCoverage435

namespace BinaryFormMoat.EntropyIntegration
open MeasureTheory ProbabilityTheory

section Checkpoint
variable {Ω A H : Type*} [Fintype Ω] [Fintype A] [Fintype H]
  [MeasurableSpace Ω] [MeasurableSingletonClass Ω]
  [MeasurableSpace A] [MeasurableSingletonClass A]
  [MeasurableSpace H] [MeasurableSingletonClass H]
  (μ : Measure Ω) [IsProbabilityMeasure μ] (V : Ω → A) (W : Ω → H)

/-- Push forward the actual checkpoint and continuation from one source law.
No new marginal law is substituted for the original experiment. -/
noncomputable def finiteCheckpointLaw : Measure (A × H) :=
  μ.map (fun ω => (V ω, W ω))

instance finiteCheckpointLaw_isProbabilityMeasure :
    IsProbabilityMeasure (finiteCheckpointLaw μ V W) := by
  unfold finiteCheckpointLaw
  infer_instance

omit [IsProbabilityMeasure μ] [Fintype A] [Fintype H] [MeasurableSingletonClass H] in
theorem finiteCheckpointLaw_fiber (a : A) :
    finiteCheckpointLaw μ V W (Prod.fst ⁻¹' {a}) = μ (V ⁻¹' {a}) := by
  rw [finiteCheckpointLaw, Measure.map_apply (measurable_of_finite _)
    (measurable_fst (MeasurableSet.singleton a))]
  rfl

omit [IsProbabilityMeasure μ] [Fintype A] [Fintype H] [MeasurableSingletonClass H] in
theorem finiteCheckpointLaw_cond (a : A) :
    (finiteCheckpointLaw μ V W)[|Prod.fst ⁻¹' {a}] =
      (μ[|V ⁻¹' {a}]).map (fun ω => (V ω, W ω)) := by
  ext E hE
  rw [cond_apply (measurable_fst (MeasurableSet.singleton a)), finiteCheckpointLaw_fiber,
    finiteCheckpointLaw, Measure.map_apply (measurable_of_finite _)
      ((measurable_fst (MeasurableSet.singleton a)).inter hE),
    Measure.map_apply (measurable_of_finite _) hE,
    cond_apply ((measurable_of_finite V) (MeasurableSet.singleton a))]
  rfl

omit [IsProbabilityMeasure μ] in
theorem finiteCheckpointLaw_identDistrib {S : Type*} [MeasurableSpace S]
    (f : A × H → S) :
    IdentDistrib f (fun ω => f (V ω, W ω)) (finiteCheckpointLaw μ V W) μ := by
  refine ⟨(measurable_of_finite _).aemeasurable, (measurable_of_finite _).aemeasurable, ?_⟩
  exact Measure.map_map (measurable_of_finite _) (measurable_of_finite _)

omit [IsProbabilityMeasure μ] in
theorem finiteCheckpointLaw_cond_identDistrib {S : Type*} [MeasurableSpace S]
    (f : A × H → S) (a : A) :
    IdentDistrib f (fun ω => f (V ω, W ω))
      ((finiteCheckpointLaw μ V W)[|Prod.fst ⁻¹' {a}]) (μ[|V ⁻¹' {a}]) := by
  refine ⟨(measurable_of_finite _).aemeasurable, (measurable_of_finite _).aemeasurable, ?_⟩
  rw [finiteCheckpointLaw_cond]
  exact Measure.map_map (measurable_of_finite _) (measurable_of_finite _)

theorem finiteCheckpointLaw_resampled_identDistrib {J S : Type*}
    [Fintype J] [MeasurableSpace S] (h₀ : H) (f : A × H → S) (j : J) :
    IdentDistrib (fun ω : A × (J → H) => f (ω.1, ω.2 j))
      (fun ω => f (V ω, W ω)) (originalResamplingLaw (finiteCheckpointLaw μ V W) h₀) μ :=
  (originalResamplingLaw_identDistrib (finiteCheckpointLaw μ V W) h₀ f j).trans
    (finiteCheckpointLaw_identDistrib μ V W f)

omit [IsProbabilityMeasure μ] in
theorem finiteCheckpointLaw_labelSubsetJointEntropy {ι R : Type*}
    [Fintype ι] [Fintype R] (G : ι × R → Type*)
    [∀ c, MeasurableSpace (G c)] (y : ∀ c, A → G c) (s : ℕ) :
    labelSubsetJointEntropy (finiteCheckpointLaw μ V W) G (fun c ah => y c ah.1) s =
      labelSubsetJointEntropy μ G (fun c ω => y c (V ω)) s := by
  unfold labelSubsetJointEntropy
  congr 1
  funext S ρ
  exact (finiteCheckpointLaw_identDistrib μ V W
    (fun ah (i : S) => y (i.1, ρ i.1) ah.1)).entropy_congr

end Checkpoint
end BinaryFormMoat.EntropyIntegration

#print axioms BinaryFormMoat.EntropyIntegration.finiteCheckpointLaw_isProbabilityMeasure
#print axioms BinaryFormMoat.EntropyIntegration.finiteCheckpointLaw_fiber
#print axioms BinaryFormMoat.EntropyIntegration.finiteCheckpointLaw_cond
#print axioms BinaryFormMoat.EntropyIntegration.finiteCheckpointLaw_identDistrib
#print axioms BinaryFormMoat.EntropyIntegration.finiteCheckpointLaw_cond_identDistrib
#print axioms BinaryFormMoat.EntropyIntegration.finiteCheckpointLaw_resampled_identDistrib
#print axioms BinaryFormMoat.EntropyIntegration.finiteCheckpointLaw_labelSubsetJointEntropy
