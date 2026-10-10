import Integrations.OriginalContinuation435
import Integrations.SharedData435

namespace BinaryFormMoat.EntropyIntegration
open MeasureTheory ProbabilityTheory

section PosteriorEntropy
variable {A H J : Type*} [Fintype A] [Fintype H] [Fintype J]
  [MeasurableSpace A] [MeasurableSingletonClass A]
  [MeasurableSpace H] [MeasurableSingletonClass H]
  (θ : Measure (A × H)) [IsProbabilityMeasure θ] (h₀ : H)

/-- Resampling keeps every observable of the original checkpoint unchanged
in distribution, even though the continuation trials are enlarged. -/
theorem originalResamplingLaw_checkpoint_identDistrib {S : Type*} [MeasurableSpace S]
    (f : A → S) (j₀ : J) :
    IdentDistrib (fun ω : A × (J → H) => f ω.1) (fun ah : A × H => f ah.1)
      (originalResamplingLaw θ h₀) θ :=
  originalResamplingLaw_identDistrib θ h₀ (fun ah => f ah.1) j₀

/-- The exact subset/label joint-entropy input can be verified on the original
checkpoint law. There is no entropy loss from constructing posterior trials. -/
theorem originalResamplingLaw_labelSubsetJointEntropy {ι R : Type*}
    [Fintype ι] [Fintype R] (G : ι × R → Type*)
    [∀ c, MeasurableSpace (G c)] (y : ∀ c, A → G c) (s : ℕ) (j₀ : J) :
    labelSubsetJointEntropy (originalResamplingLaw (J := J) θ h₀) G (fun c ω => y c ω.1) s =
      labelSubsetJointEntropy θ G (fun c ah => y c ah.1) s := by
  unfold labelSubsetJointEntropy
  congr 1
  funext S ρ
  exact (originalResamplingLaw_checkpoint_identDistrib θ h₀
    (fun a (i : S) => y (i.1, ρ i.1) a) j₀).entropy_congr

omit [IsProbabilityMeasure θ] [MeasurableSingletonClass A] in
/-- A finite continuation alphabet gives a concrete common-data entropy
bound. Conditional independence is not needed for this cardinality bound. -/
theorem originalResamplingLaw_data_entropy_le :
    entropy (Prod.snd : A × (J → H) → J → H) (originalResamplingLaw θ h₀) ≤
      (Fintype.card J : ℝ) * Real.log (Fintype.card H) := by
  classical
  have h := entropy_le_log_card (Prod.snd : A × (J → H) → J → H)
    (originalResamplingLaw θ h₀)
  simpa only [Fintype.card_fun, Nat.cast_pow, Real.log_pow] using h

omit [IsProbabilityMeasure θ] [MeasurableSingletonClass A] in
/-- Encode each continuation by a fixed-length word. An injective encoding
preserves data entropy and charges the word length once per trial. -/
theorem originalResamplingLaw_encoded_data_entropy_le {K : Type*}
    [Fintype K] [MeasurableSpace K] [MeasurableSingletonClass K]
    (L : ℕ) (encode : H → (Fin L → K)) (hinj : Function.Injective encode) :
    entropy (Prod.snd : A × (J → H) → J → H) (originalResamplingLaw θ h₀) ≤
      (Fintype.card J : ℝ) * L * Real.log (Fintype.card K) := by
  classical
  let enc := fun h : J → H => fun j => encode (h j)
  have hi : Function.Injective enc := by
    intro h h' he
    funext j
    exact hinj (congrFun he j)
  have he := entropy_comp_of_injective (originalResamplingLaw θ h₀)
    measurable_snd enc hi
  have hb := entropy_le_log_card (enc ∘ (Prod.snd : A × (J → H) → J → H))
    (originalResamplingLaw θ h₀)
  rw [he] at hb
  simpa only [Fintype.card_fun, Fintype.card_fin, Nat.cast_pow, Real.log_pow,
    mul_assoc] using hb

end PosteriorEntropy
end BinaryFormMoat.EntropyIntegration

#print axioms BinaryFormMoat.EntropyIntegration.originalResamplingLaw_checkpoint_identDistrib
#print axioms BinaryFormMoat.EntropyIntegration.originalResamplingLaw_labelSubsetJointEntropy
#print axioms BinaryFormMoat.EntropyIntegration.originalResamplingLaw_data_entropy_le
#print axioms BinaryFormMoat.EntropyIntegration.originalResamplingLaw_encoded_data_entropy_le
