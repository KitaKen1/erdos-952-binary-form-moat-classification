import Integrations.PFRInformation435

namespace BinaryFormMoat.EntropyIntegration
open MeasureTheory ProbabilityTheory

/-- A lossless finite observation history, newest entry first. -/
def observationHistory {Ω T : Type*} (Y : ℕ → Ω → T) : (n : ℕ) → Ω → (Fin n → T)
  | 0 => fun _ => Fin.elim0
  | n + 1 => fun ω => Fin.cons (Y n ω) (observationHistory Y n ω)

theorem measurable_observationHistory {Ω T : Type*}
    [MeasurableSpace Ω] [MeasurableSpace T] [MeasurableSingletonClass T] [Fintype T]
    (Y : ℕ → Ω → T) (hY : ∀ i, Measurable (Y i)) (n : ℕ) :
    Measurable (observationHistory Y n) := by
  induction n with
  | zero => exact measurable_const
  | succ n ih =>
    exact (measurable_of_finite (Fin.consEquiv (fun _ : Fin (n + 1) => T))).comp
      ((hY n).prodMk ih)

theorem condEntropy_observationHistory_zero {Ω S T : Type*}
    [MeasurableSpace Ω] [MeasurableSpace S] [MeasurableSingletonClass S] [Fintype S]
    [MeasurableSpace T] [MeasurableSingletonClass T] [Fintype T]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (X : Ω → S) (hX : Measurable X)
    (Y : ℕ → Ω → T) :
    condEntropy X (observationHistory Y 0) μ = entropy X μ := by
  change condEntropy X (fun _ : Ω => (Fin.elim0 : Fin 0 → T)) μ = entropy X μ
  rw [chain_rule'' μ hX (measurable_const : Measurable
    (fun _ : Ω => (Fin.elim0 : Fin 0 → T)))]
  have hp : entropy (fun ω => (X ω, (Fin.elim0 : Fin 0 → T))) μ = entropy X μ :=
    entropy_comp_of_injective μ hX (fun s => (s, (Fin.elim0 : Fin 0 → T)))
      (fun _ _ h => congrArg Prod.fst h)
  simpa only [observationHistory, entropy_const, sub_zero] using hp

/-- Chain rule under one fixed law; prior histories may depend on X. -/
theorem information_observationHistory_step {Ω S T : Type*}
    [MeasurableSpace Ω] [MeasurableSpace S] [MeasurableSingletonClass S] [Fintype S]
    [MeasurableSpace T] [MeasurableSingletonClass T] [Fintype T]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (X : Ω → S) (hX : Measurable X)
    (Y : ℕ → Ω → T) (hY : ∀ i, Measurable (Y i)) (n : ℕ) :
    condMutualInfo X (Y n) (observationHistory Y n) μ =
      condEntropy X (observationHistory Y n) μ -
        condEntropy X (observationHistory Y (n + 1)) μ := by
  have hh := measurable_observationHistory Y hY n
  let e := Fin.consEquiv (fun _ : Fin (n + 1) => T)
  have hn := condEntropy_of_injective' μ hX ((hY n).prodMk hh) e e.injective
    ((measurable_of_finite e).comp ((hY n).prodMk hh))
  change condEntropy X (observationHistory Y (n + 1)) μ =
    condEntropy X (fun ω => (Y n ω, observationHistory Y n ω)) μ at hn
  rw [hn]
  exact condMutualInfo_eq' hX (hY n) hh μ

theorem information_observationHistory_telescope {Ω S T : Type*}
    [MeasurableSpace Ω] [MeasurableSpace S] [MeasurableSingletonClass S] [Fintype S]
    [MeasurableSpace T] [MeasurableSingletonClass T] [Fintype T]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (X : Ω → S) (hX : Measurable X)
    (Y : ℕ → Ω → T) (hY : ∀ i, Measurable (Y i)) (n : ℕ) :
    (∑ i ∈ Finset.range n, condMutualInfo X (Y i) (observationHistory Y i) μ) =
      entropy X μ - condEntropy X (observationHistory Y n) μ := by
  induction n with
  | zero => simp [condEntropy_observationHistory_zero μ X hX Y]
  | succ n ih =>
    rw [Finset.sum_range_succ, ih, information_observationHistory_step μ X hX Y hY n]
    ring

theorem information_observationHistory_sum_le_entropy {Ω S T : Type*}
    [MeasurableSpace Ω] [MeasurableSpace S] [MeasurableSingletonClass S] [Fintype S]
    [MeasurableSpace T] [MeasurableSingletonClass T] [Fintype T]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (X : Ω → S) (hX : Measurable X)
    (Y : ℕ → Ω → T) (hY : ∀ i, Measurable (Y i)) (n : ℕ) :
    (∑ i ∈ Finset.range n, condMutualInfo X (Y i) (observationHistory Y i) μ) ≤
      entropy X μ := by
  rw [information_observationHistory_telescope μ X hX Y hY n]
  exact sub_le_self _ (condEntropy_nonneg _ _ _)

/-- Every information lower bound is charged to the same finite entropy budget. -/
theorem observationHistory_gains_le_entropy {Ω S T : Type*}
    [MeasurableSpace Ω] [MeasurableSpace S] [MeasurableSingletonClass S] [Fintype S]
    [MeasurableSpace T] [MeasurableSingletonClass T] [Fintype T]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (X : Ω → S) (hX : Measurable X)
    (Y : ℕ → Ω → T) (hY : ∀ i, Measurable (Y i)) (n : ℕ) (gain : ℕ → ℝ)
    (hgain : ∀ i < n, gain i ≤ condMutualInfo X (Y i) (observationHistory Y i) μ) :
    (∑ i ∈ Finset.range n, gain i) ≤ entropy X μ := by
  apply le_trans _ (information_observationHistory_sum_le_entropy μ X hX Y hY n)
  exact Finset.sum_le_sum (fun i hi => hgain i (Finset.mem_range.mp hi))

theorem observationHistory_list_gains_le_entropy {Ω S T : Type*}
    [MeasurableSpace Ω] [MeasurableSpace S] [MeasurableSingletonClass S] [Fintype S]
    [MeasurableSpace T] [MeasurableSingletonClass T] [Fintype T]
    [MeasurableSpace Bool] [MeasurableSingletonClass Bool]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (X : Ω → S) (hX : Measurable X)
    (Y : ℕ → Ω → T) (hY : ∀ i, Measurable (Y i)) (n : ℕ)
    (A : Finset S) (hA : A.Nonempty) (hsupport : ∀ᵐ ω ∂μ, X ω ∈ A)
    (L : (i : ℕ) → T × (Fin i → T) → Finset S) (M : ℕ → ℕ) (ε baseline : ℕ → ℝ)
    (hM : ∀ i < n, 1 ≤ M i) (hsize : ∀ i < n, ∀ y, (L i y).card ≤ M i)
    (herr : ∀ i < n, μ.real {ω | X ω ∉ L i (Y i ω, observationHistory Y i ω)} ≤ ε i)
    (hbase : ∀ i < n, baseline i ≤ condEntropy X (observationHistory Y i) μ) :
    (∑ i ∈ Finset.range n, (baseline i - Real.log 2 - Real.log (M i : ℝ) -
      ε i * Real.log (A.card : ℝ))) ≤ entropy X μ := by
  apply observationHistory_gains_le_entropy μ X hX Y hY n
  intro i hi
  have h := condMutualInfo_ge_list_size_error_of_ae_support μ X (Y i)
    (observationHistory Y i) A hA (L i) hX (hY i)
    (measurable_observationHistory Y hY i) hsupport (M i) (hM i hi)
    (hsize i hi) (ε i) (herr i hi)
  have hb := hbase i hi
  linarith

theorem observationHistory_information_budget_contradiction {Ω S T : Type*}
    [MeasurableSpace Ω] [MeasurableSpace S] [MeasurableSingletonClass S] [Fintype S]
    [MeasurableSpace T] [MeasurableSingletonClass T] [Fintype T]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (X : Ω → S) (hX : Measurable X)
    (Y : ℕ → Ω → T) (hY : ∀ i, Measurable (Y i)) (n : ℕ) (gain : ℕ → ℝ) (budget : ℝ)
    (hgain : ∀ i < n, gain i ≤ condMutualInfo X (Y i) (observationHistory Y i) μ)
    (hbudget : entropy X μ ≤ budget) (hexcess : budget < ∑ i ∈ Finset.range n, gain i) :
    False := by
  exact (not_lt_of_ge ((observationHistory_gains_le_entropy μ X hX Y hY n gain hgain).trans
    hbudget)) hexcess

/-- The orientation used for residues revealing a single walk word. -/
theorem observationHistory_residue_information_le_word_entropy {Ω S T : Type*}
    [MeasurableSpace Ω] [MeasurableSpace S] [MeasurableSingletonClass S] [Fintype S]
    [MeasurableSpace T] [MeasurableSingletonClass T] [Fintype T]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (W : Ω → S) (hW : Measurable W)
    (Y : ℕ → Ω → T) (hY : ∀ i, Measurable (Y i)) (n : ℕ) :
    (∑ i ∈ Finset.range n, condMutualInfo (Y i) W (observationHistory Y i) μ) ≤
      entropy W μ := by
  calc
    _ = ∑ i ∈ Finset.range n, condMutualInfo W (Y i) (observationHistory Y i) μ := by
      apply Finset.sum_congr rfl
      intro i _
      exact condMutualInfo_comm (hY i) hW _ μ
    _ ≤ _ := information_observationHistory_sum_le_entropy μ W hW Y hY n

theorem observationHistory_residue_information_le_word_budget {Ω A T : Type*}
    [MeasurableSpace Ω] [MeasurableSpace A] [MeasurableSingletonClass A] [Fintype A]
    [MeasurableSpace T] [MeasurableSingletonClass T] [Fintype T]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (L : ℕ) (W : Ω → (Fin L → A))
    (hW : Measurable W) (Y : ℕ → Ω → T) (hY : ∀ i, Measurable (Y i)) (n : ℕ) :
    (∑ i ∈ Finset.range n, condMutualInfo (Y i) W (observationHistory Y i) μ) ≤
      (L : ℝ) * Real.log (Fintype.card A) := by
  apply (observationHistory_residue_information_le_word_entropy μ W hW Y hY n).trans
  have h := entropy_le_log_card W μ
  simpa only [Fintype.card_fun, Fintype.card_fin, Nat.cast_pow, Real.log_pow] using h

end BinaryFormMoat.EntropyIntegration

#print axioms BinaryFormMoat.EntropyIntegration.measurable_observationHistory
#print axioms BinaryFormMoat.EntropyIntegration.condEntropy_observationHistory_zero
#print axioms BinaryFormMoat.EntropyIntegration.information_observationHistory_step
#print axioms BinaryFormMoat.EntropyIntegration.information_observationHistory_telescope
#print axioms BinaryFormMoat.EntropyIntegration.information_observationHistory_sum_le_entropy
#print axioms BinaryFormMoat.EntropyIntegration.observationHistory_gains_le_entropy
#print axioms BinaryFormMoat.EntropyIntegration.observationHistory_list_gains_le_entropy
#print axioms BinaryFormMoat.EntropyIntegration.observationHistory_information_budget_contradiction
#print axioms BinaryFormMoat.EntropyIntegration.observationHistory_residue_information_le_word_entropy
#print axioms BinaryFormMoat.EntropyIntegration.observationHistory_residue_information_le_word_budget
