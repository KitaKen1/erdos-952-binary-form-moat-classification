import Integrations.PFR435

namespace BinaryFormMoat.EntropyIntegration
open MeasureTheory ProbabilityTheory

theorem entropy_le_log_max_card_of_mem {Ω S : Type*}
    [MeasurableSpace Ω] [MeasurableSpace S] [DiscreteMeasurableSpace S]
    (μ : Measure Ω) (X : Ω → S) (A : Finset S) (hX : Measurable X)
    (hmem : ∀ᵐ ω ∂μ, X ω ∈ A) :
    entropy X μ ≤ Real.log ((max 1 A.card : ℕ) : ℝ) := by
  apply (entropy_le_log_card_of_mem hX hmem).trans
  by_cases hzero : A.card = 0
  · simp [hzero]
  · apply Real.log_le_log
    · exact_mod_cast Nat.pos_of_ne_zero hzero
    · exact_mod_cast (le_max_right 1 A.card)

/-- Summing joint fibers over the observation gives exactly the flag mass. -/
theorem sum_pair_fiber_real {Ω S T : Type*}
    [MeasurableSpace Ω] [MeasurableSpace S] [MeasurableSingletonClass S]
    [MeasurableSpace T] [MeasurableSingletonClass T] [Fintype T]
    (μ : Measure Ω) [IsFiniteMeasure μ] (E : Ω → S) (Y : Ω → T)
    (hE : Measurable E) (hY : Measurable Y) (e : S) :
    (∑ y, μ.real ((fun ω => (E ω, Y ω)) ⁻¹' {(e, y)})) =
      μ.real (E ⁻¹' {e}) := by
  classical
  have hunion : (⋃ y, (fun ω => (E ω, Y ω)) ⁻¹' {(e, y)}) = E ⁻¹' {e} := by
    ext ω
    simp
  rw [← hunion, measureReal_iUnion_fintype]
  · intro y y' hne
    apply Set.disjoint_left.mpr
    intro ω hω hω'
    exact hne ((congrArg Prod.snd hω).symm.trans (congrArg Prod.snd hω'))
  · exact fun y => (hE.prodMk hY) (MeasurableSet.singleton (e, y))

/-- Zero-mass success fibers are covered by the same conditional-support proof. -/
theorem success_fiber_entropy_le {Ω S T : Type*}
    [MeasurableSpace Ω] [MeasurableSpace S] [MeasurableSingletonClass S] [Fintype S]
    [MeasurableSpace T] [MeasurableSingletonClass T]
    [MeasurableSpace Bool] [MeasurableSingletonClass Bool]
    (μ : Measure Ω) (X : Ω → S) (Y : Ω → T) (E : Ω → Bool) (L : T → Finset S)
    (hX : Measurable X) (hY : Measurable Y) (hE : Measurable E)
    (hgood : ∀ ω, E ω = false → X ω ∈ L (Y ω)) (y : T) :
    entropy X (μ[|(fun ω => (E ω, Y ω)) ← (false, y)]) ≤
      Real.log ((max 1 (L y).card : ℕ) : ℝ) := by
  apply entropy_le_log_max_card_of_mem _ X (L y) hX
  apply ae_cond_of_forall_mem ((hE.prodMk hY) (MeasurableSet.singleton (false, y)))
  intro ω hω
  have he : E ω = false := congrArg Prod.fst hω
  have hy : Y ω = y := congrArg Prod.snd hω
  simpa only [hy] using hgood ω he

/-- The error cost is weighted by its actual probability under the same law.
No conditional independence or nonempty-list premise is needed. -/
theorem condEntropy_le_list_with_flag {Ω S T : Type*}
    [MeasurableSpace Ω] [MeasurableSpace S] [MeasurableSingletonClass S] [Fintype S]
    [MeasurableSpace T] [MeasurableSingletonClass T] [Fintype T]
    [MeasurableSpace Bool] [MeasurableSingletonClass Bool]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : Ω → S) (Y : Ω → T) (E : Ω → Bool) (L : T → Finset S)
    (hX : Measurable X) (hY : Measurable Y) (hE : Measurable E)
    (hgood : ∀ ω, E ω = false → X ω ∈ L (Y ω)) :
    condEntropy X Y μ ≤ Real.log 2 +
      (∑ y, μ.real (Y ⁻¹' {y}) * Real.log ((max 1 (L y).card : ℕ) : ℝ)) +
      μ.real (E ⁻¹' {true}) * Real.log (Fintype.card S) := by
  classical
  let Z := fun ω => (E ω, Y ω)
  have hZ : Measurable Z := hE.prodMk hY
  have ht : (∑ y, μ.real (Z ⁻¹' {(true, y)}) *
      entropy X (μ[|Z ← (true, y)])) ≤
      μ.real (E ⁻¹' {true}) * Real.log (Fintype.card S) := by
    calc
      _ ≤ ∑ y, μ.real (Z ⁻¹' {(true, y)}) * Real.log (Fintype.card S) := by
        apply Finset.sum_le_sum
        intro y _
        exact mul_le_mul_of_nonneg_left (entropy_le_log_card X _) measureReal_nonneg
      _ = _ := by
        rw [← Finset.sum_mul, sum_pair_fiber_real μ E Y hE hY true]
  have hf : (∑ y, μ.real (Z ⁻¹' {(false, y)}) *
      entropy X (μ[|Z ← (false, y)])) ≤
      ∑ y, μ.real (Y ⁻¹' {y}) * Real.log ((max 1 (L y).card : ℕ) : ℝ) := by
    apply Finset.sum_le_sum
    intro y _
    have hlog : 0 ≤ Real.log ((max 1 (L y).card : ℕ) : ℝ) := by
      apply Real.log_nonneg
      exact_mod_cast (le_max_left 1 (L y).card)
    calc
      _ ≤ μ.real (Z ⁻¹' {(false, y)}) * Real.log ((max 1 (L y).card : ℕ) : ℝ) :=
        mul_le_mul_of_nonneg_left (success_fiber_entropy_le μ X Y E L hX hY hE hgood y)
          measureReal_nonneg
      _ ≤ _ := mul_le_mul_of_nonneg_right
        (measureReal_mono (fun ω hω => congrArg Prod.snd hω)) hlog
  have hbound : condEntropy X Z μ ≤
      (∑ y, μ.real (Y ⁻¹' {y}) * Real.log ((max 1 (L y).card : ℕ) : ℝ)) +
      μ.real (E ⁻¹' {true}) * Real.log (Fintype.card S) := by
    rw [condEntropy_eq_sum_fintype X Z μ hZ, Fintype.sum_prod_type, Fintype.sum_bool]
    linarith
  have h := (condEntropy_le_error_flag μ X Y E hX hY hE).trans
    (add_le_add (le_refl (Real.log 2)) hbound)
  simpa only [Z, add_assoc] using h

noncomputable def listErrorFlag {Ω S T : Type*} (X : Ω → S) (Y : Ω → T)
    (L : T → Finset S) (ω : Ω) : Bool := by
  classical
  exact if X ω ∈ L (Y ω) then false else true

theorem measurable_listErrorFlag {Ω S T : Type*}
    [MeasurableSpace Ω] [MeasurableSpace S] [MeasurableSingletonClass S] [Fintype S]
    [MeasurableSpace T] [MeasurableSingletonClass T] [Fintype T] [MeasurableSpace Bool]
    (X : Ω → S) (Y : Ω → T) (L : T → Finset S)
    (hX : Measurable X) (hY : Measurable Y) : Measurable (listErrorFlag X Y L) := by
  classical
  exact (measurable_of_finite (fun z : S × T => if z.1 ∈ L z.2 then false else true)).comp
    (hX.prodMk hY)

theorem listErrorFlag_false_mem {Ω S T : Type*} (X : Ω → S) (Y : Ω → T)
    (L : T → Finset S) (ω : Ω) (h : listErrorFlag X Y L ω = false) : X ω ∈ L (Y ω) := by
  classical
  by_contra hn
  simp [listErrorFlag, hn] at h

theorem listErrorFlag_true_preimage {Ω S T : Type*} (X : Ω → S) (Y : Ω → T)
    (L : T → Finset S) :
    listErrorFlag X Y L ⁻¹' {true} = {ω | X ω ∉ L (Y ω)} := by
  classical
  ext ω
  simp [listErrorFlag]

/-- Error-aware conditional list bound, including empty lists and zero fibers. -/
theorem condEntropy_le_error_aware_list {Ω S T : Type*}
    [MeasurableSpace Ω] [MeasurableSpace S] [MeasurableSingletonClass S] [Fintype S]
    [MeasurableSpace T] [MeasurableSingletonClass T] [Fintype T]
    [MeasurableSpace Bool] [MeasurableSingletonClass Bool]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : Ω → S) (Y : Ω → T) (L : T → Finset S)
    (hX : Measurable X) (hY : Measurable Y) :
    condEntropy X Y μ ≤ Real.log 2 +
      (∑ y, μ.real (Y ⁻¹' {y}) * Real.log ((max 1 (L y).card : ℕ) : ℝ)) +
      μ.real {ω | X ω ∉ L (Y ω)} * Real.log (Fintype.card S) := by
  simpa only [listErrorFlag_true_preimage] using
    condEntropy_le_list_with_flag μ X Y (listErrorFlag X Y L) L hX hY
      (measurable_listErrorFlag X Y L hX hY) (listErrorFlag_false_mem X Y L)

/-- Almost-sure list support needs no error flag or log(2) penalty. -/
theorem condEntropy_le_log_list_of_ae_mem {Ω S T : Type*}
    [MeasurableSpace Ω] [MeasurableSpace S] [MeasurableSingletonClass S] [Fintype S]
    [MeasurableSpace T] [MeasurableSingletonClass T] [Fintype T]
    (μ : Measure Ω) [IsFiniteMeasure μ]
    (X : Ω → S) (Y : Ω → T) (L : T → Finset S)
    (hX : Measurable X) (hY : Measurable Y)
    (hmem : ∀ᵐ ω ∂μ, X ω ∈ L (Y ω)) :
    condEntropy X Y μ ≤
      ∑ y, μ.real (Y ⁻¹' {y}) * Real.log ((max 1 (L y).card : ℕ) : ℝ) := by
  classical
  rw [condEntropy_eq_sum_fintype X Y μ hY]
  apply Finset.sum_le_sum
  intro y _
  apply mul_le_mul_of_nonneg_left _ measureReal_nonneg
  apply entropy_le_log_max_card_of_mem _ X (L y) hX
  have hmem' : ∀ᵐ ω ∂μ[|Y ← y], X ω ∈ L (Y ω) :=
    hmem.filter_mono cond_absolutelyContinuous.ae_le
  filter_upwards [hmem', ae_cond_mem (hY (MeasurableSet.singleton y))] with ω hω hy
  simpa only [show Y ω = y from hy] using hω

/-- A directly usable bound from a maximum list size and an error quota. -/
theorem condEntropy_le_list_size_error {Ω S T : Type*}
    [MeasurableSpace Ω] [MeasurableSpace S] [MeasurableSingletonClass S] [Fintype S]
    [MeasurableSpace T] [MeasurableSingletonClass T] [Fintype T]
    [MeasurableSpace Bool] [MeasurableSingletonClass Bool]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : Ω → S) (Y : Ω → T) (L : T → Finset S)
    (hX : Measurable X) (hY : Measurable Y) (M : ℕ) (hM : 1 ≤ M)
    (hsize : ∀ y, (L y).card ≤ M) (ε : ℝ)
    (herr : μ.real {ω | X ω ∉ L (Y ω)} ≤ ε) :
    condEntropy X Y μ ≤ Real.log 2 + Real.log (M : ℝ) +
      ε * Real.log (Fintype.card S) := by
  classical
  have hs : (∑ y, μ.real (Y ⁻¹' {y}) * Real.log ((max 1 (L y).card : ℕ) : ℝ)) ≤
      Real.log (M : ℝ) := by
    calc
      _ ≤ ∑ y, μ.real (Y ⁻¹' {y}) * Real.log (M : ℝ) := by
        apply Finset.sum_le_sum
        intro y _
        apply mul_le_mul_of_nonneg_left _ measureReal_nonneg
        apply Real.log_le_log
        · exact_mod_cast (show 0 < max 1 (L y).card by omega)
        · exact_mod_cast (max_le hM (hsize y))
      _ = _ := by
        rw [← Finset.sum_mul, sum_measureReal_preimage_singleton _
          (fun y _ => hY (MeasurableSet.singleton y))]
        simp
  have hq : 0 ≤ Real.log (Fintype.card S : ℝ) := by
    by_cases hz : Fintype.card S = 0
    · simp [hz]
    · exact Real.log_nonneg (by exact_mod_cast (Nat.pos_of_ne_zero hz))
  have he := mul_le_mul_of_nonneg_right herr hq
  have h := condEntropy_le_error_aware_list μ X Y L hX hY
  linarith

/-- Conditioning pays the reciprocal of the conditioning event's mass.
It does not preserve an unconditional error estimate unchanged. -/
theorem conditioned_event_real_le {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsFiniteMeasure μ] (B D : Set Ω) (hB : MeasurableSet B) :
    (μ[|B]).real D ≤ μ.real D / μ.real B := by
  calc
    _ = (μ.real B)⁻¹ * μ.real (B ∩ D) := cond_real_apply hB μ D
    _ ≤ (μ.real B)⁻¹ * μ.real D := mul_le_mul_of_nonneg_left
      (measureReal_mono Set.inter_subset_right) (inv_nonneg.mpr measureReal_nonneg)
    _ = _ := by rw [div_eq_mul_inv, mul_comm]

/-- A safe one-event conditioning transfer for the list-size/error bound.
The original error quota is used only after paying 1/Pr(B). -/
theorem conditioned_condEntropy_le_list_size_error {Ω S T : Type*}
    [MeasurableSpace Ω] [MeasurableSpace S] [MeasurableSingletonClass S] [Fintype S]
    [MeasurableSpace T] [MeasurableSingletonClass T] [Fintype T]
    [MeasurableSpace Bool] [MeasurableSingletonClass Bool]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : Ω → S) (Y : Ω → T) (L : T → Finset S)
    (hX : Measurable X) (hY : Measurable Y) (M : ℕ) (hM : 1 ≤ M)
    (hsize : ∀ y, (L y).card ≤ M) (B : Set Ω) (hB : MeasurableSet B)
    (hpos : 0 < μ.real B) (δ : ℝ)
    (herr : μ.real {ω | X ω ∉ L (Y ω)} ≤ δ) :
    condEntropy X Y (μ[|B]) ≤ Real.log 2 + Real.log (M : ℝ) +
      (δ / μ.real B) * Real.log (Fintype.card S) := by
  let : IsProbabilityMeasure μ[|B] := cond_isProbabilityMeasure_of_real (ne_of_gt hpos)
  apply condEntropy_le_list_size_error (μ[|B]) X Y L hX hY M hM hsize (δ / μ.real B)
  exact (conditioned_event_real_le μ B _ hB).trans
    (div_le_div_of_nonneg_right herr hpos.le)

end BinaryFormMoat.EntropyIntegration

#print axioms BinaryFormMoat.EntropyIntegration.entropy_le_log_max_card_of_mem
#print axioms BinaryFormMoat.EntropyIntegration.sum_pair_fiber_real
#print axioms BinaryFormMoat.EntropyIntegration.success_fiber_entropy_le
#print axioms BinaryFormMoat.EntropyIntegration.condEntropy_le_list_with_flag
#print axioms BinaryFormMoat.EntropyIntegration.measurable_listErrorFlag
#print axioms BinaryFormMoat.EntropyIntegration.listErrorFlag_false_mem
#print axioms BinaryFormMoat.EntropyIntegration.listErrorFlag_true_preimage
#print axioms BinaryFormMoat.EntropyIntegration.condEntropy_le_error_aware_list
#print axioms BinaryFormMoat.EntropyIntegration.condEntropy_le_log_list_of_ae_mem
#print axioms BinaryFormMoat.EntropyIntegration.condEntropy_le_list_size_error
#print axioms BinaryFormMoat.EntropyIntegration.conditioned_event_real_le
#print axioms BinaryFormMoat.EntropyIntegration.conditioned_condEntropy_le_list_size_error
