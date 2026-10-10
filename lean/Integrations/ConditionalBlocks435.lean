import Integrations.InformationHistory435

namespace BinaryFormMoat.EntropyIntegration
open MeasureTheory ProbabilityTheory

/-- Chronological prefixes, so index arithmetic agrees with word blocks. -/
def blockPrefix {Ω S : Type*} (Y : ℕ → Ω → S) (n : ℕ) : Ω → (Fin n → S) :=
  fun ω i => Y i ω

theorem measurable_blockPrefix {Ω S : Type*}
    [MeasurableSpace Ω] [MeasurableSpace S]
    (Y : ℕ → Ω → S) (hY : ∀ i, Measurable (Y i)) (n : ℕ) :
    Measurable (blockPrefix Y n) :=
  Measurable.of_eval (fun i => hY i)

/-- Exact conditional chain rule with the original side observation retained
in every prefix. No independence or stationarity is assumed. -/
theorem condEntropy_blockPrefix_chain {Ω S T : Type*}
    [MeasurableSpace Ω] [MeasurableSpace S] [MeasurableSingletonClass S] [Fintype S]
    [MeasurableSpace T] [MeasurableSingletonClass T] [Fintype T]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Y : ℕ → Ω → S) (hY : ∀ i, Measurable (Y i))
    (Z : Ω → T) (hZ : Measurable Z) (n : ℕ) :
    condEntropy (blockPrefix Y n) Z μ =
      ∑ i ∈ Finset.range n,
        condEntropy (Y i) (fun ω => (blockPrefix Y i ω, Z ω)) μ := by
  induction n with
  | zero =>
    have he : blockPrefix Y 0 = fun _ : Ω => (Fin.elim0 : Fin 0 → S) := by
      funext ω i
      exact Fin.elim0 i
    simp [he, condEntropy]
  | succ n ih =>
    let e := Fin.snocEquiv (fun _ : Fin (n + 1) => S)
    have hp := measurable_blockPrefix Y hY n
    have he : blockPrefix Y (n + 1) =
        e ∘ (fun ω => (Y n ω, blockPrefix Y n ω)) := by
      funext ω i
      cases i using Fin.lastCases with
      | last => simp [e, Fin.snocEquiv, blockPrefix]
      | cast i => simp [e, Fin.snocEquiv, blockPrefix]
    rw [he, condEntropy_comp_of_injective μ ((hY n).prodMk hp) e e.injective,
      cond_chain_rule μ (hY n) hp hZ, ih, Finset.sum_range_succ]

/-- Removing the prefix is justified only when it reconstructs the new
observation together with the initial side information. -/
theorem condEntropy_blockPrefix_le_reconstructed {Ω S T U : Type*}
    [MeasurableSpace Ω] [MeasurableSpace S] [MeasurableSingletonClass S] [Fintype S]
    [MeasurableSpace T] [MeasurableSingletonClass T] [Fintype T]
    [MeasurableSpace U] [MeasurableSingletonClass U] [Fintype U]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Y : ℕ → Ω → S) (hY : ∀ i, Measurable (Y i))
    (Z : Ω → T) (hZ : Measurable Z) (R : ℕ → Ω → U)
    (recover : (i : ℕ) → (Fin i → S) × T → U) (n : ℕ)
    (hrec : ∀ i < n, ∀ ω, R i ω = recover i (blockPrefix Y i ω, Z ω)) :
    condEntropy (blockPrefix Y n) Z μ ≤
      ∑ i ∈ Finset.range n, condEntropy (Y i) (R i) μ := by
  rw [condEntropy_blockPrefix_chain μ Y hY Z hZ]
  apply Finset.sum_le_sum
  intro i hi
  have hr : R i = recover i ∘ (fun ω => (blockPrefix Y i ω, Z ω)) :=
    funext (hrec i (Finset.mem_range.mp hi))
  rw [hr]
  exact condEntropy_comp_ge μ ((measurable_blockPrefix Y hY i).prodMk hZ)
    (hY i) (recover i)

end BinaryFormMoat.EntropyIntegration

#print axioms BinaryFormMoat.EntropyIntegration.measurable_blockPrefix
#print axioms BinaryFormMoat.EntropyIntegration.condEntropy_blockPrefix_chain
#print axioms BinaryFormMoat.EntropyIntegration.condEntropy_blockPrefix_le_reconstructed
