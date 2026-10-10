import PFR.ForMathlib.Entropy.Basic

namespace BinaryFormMoat.EntropyIntegration
open MeasureTheory ProbabilityTheory

/-- Adding a Boolean error flag costs at most log(2). This upper bound does
not require proving that the flag is determined by X and Y. The same measure
is used throughout; no conditional independence assumption is introduced. -/
theorem condEntropy_le_error_flag {Ω S T : Type*}
    [MeasurableSpace Ω] [MeasurableSpace S] [MeasurableSingletonClass S] [Fintype S]
    [MeasurableSpace T] [MeasurableSingletonClass T] [Fintype T]
    [MeasurableSpace Bool] [MeasurableSingletonClass Bool]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : Ω → S) (Y : Ω → T) (E : Ω → Bool)
    (hX : Measurable X) (hY : Measurable Y) (hE : Measurable E) :
    condEntropy X Y μ ≤ Real.log 2 + condEntropy X (fun ω => (E ω, Y ω)) μ := by
  have hfirst := cond_chain_rule' μ hX hE hY
  have hsecond := cond_chain_rule μ hX hE hY
  have hn := condEntropy_nonneg E (fun ω => (X ω, Y ω)) μ
  have he : condEntropy E Y μ ≤ Real.log 2 := by
    simpa using condEntropy_le_log_card E Y μ
  linarith

end BinaryFormMoat.EntropyIntegration

#print axioms ProbabilityTheory.cond_chain_rule
#print axioms ProbabilityTheory.cond_chain_rule'
#print axioms ProbabilityTheory.condEntropy_nonneg
#print axioms ProbabilityTheory.condEntropy_le_log_card
#print axioms ProbabilityTheory.condEntropy_eq_sum_fintype
#print axioms ProbabilityTheory.entropy_le_log_card_of_mem
#print axioms BinaryFormMoat.EntropyIntegration.condEntropy_le_error_flag
