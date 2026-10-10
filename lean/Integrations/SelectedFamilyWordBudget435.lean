import Integrations.FiniteClampedWords435

noncomputable section
open scoped Classical
namespace BinaryFormMoat.EntropyIntegration
open MeasureTheory ProbabilityTheory

/-- Sort the ACTUAL selected family, faithfully embed each target, keep its
exact earlier prior, and add one zero final observation. The natural-time
law is unchanged. This is an equality, not an information monotonicity claim. -/
theorem selectedFamily_dyadic_information_sum
    (I : Finset ℕ) (K : I → Type*) [∀ i, AddCommGroup (K i)] [∀ i, Fintype (K i)]
    [∀ i, MeasurableSpace (K i)] [∀ i, MeasurableSingletonClass (K i)]
    (Φ : ∀ i, Point →+ K i) (μ : Measure ℕ) [IsProbabilityMeasure μ]
    (z : ℕ → Point) (R : ℕ) (hstep : ∀ t, sqDist (z (t + 1)) (z t) ≤ (R : ℤ))
    (l : I → ℕ) :
    let e := selectedFamilyOrder I
    let K' := fun k => K (e k)
    let φ := finiteFamilyBatchHom K' (fun k => Φ (e k))
    let level := finiteClampedLevel (fun k => l (e k))
    (∑ i : I,
      condMutualInfo (fun t => Φ i (z t)) (wordAt (walkLetters z R hstep) (2 ^ l i))
        (fun t => maskedPriorHom K Φ (Finset.univ.filter (fun j : I => j.val < i.val)) (z t)) μ /
        (2 ^ l i : ℕ)) =
      ∑ n ∈ Finset.range (I.card + 1),
        condMutualInfo (fun t => φ n (z t)) (wordAt (walkLetters z R hstep) (2 ^ level n))
          (observationHistory (fun j t => φ j (z t)) n) μ / (2 ^ level n : ℕ) := by
  dsimp only
  let e := selectedFamilyOrder I
  let K' := fun k => K (e k)
  let φ := finiteFamilyBatchHom K' (fun k => Φ (e k))
  let level := finiteClampedLevel (fun k => l (e k))
  let H := fun n => condMutualInfo (fun t => φ n (z t))
    (wordAt (walkLetters z R hstep) (2 ^ level n))
    (observationHistory (fun j t => φ j (z t)) n) μ / (2 ^ level n : ℕ)
  have hz : H I.card = 0 := by
    dsimp only [H]
    rw [show condMutualInfo (fun t => φ I.card (z t))
      (wordAt (walkLetters z R hstep) (2 ^ level I.card))
      (observationHistory (fun j t => φ j (z t)) I.card) μ = 0 from
        finiteFamilyBatch_information_dummy K' (fun k => Φ (e k)) μ z _ _ I.card (le_refl _)]
    exact zero_div _
  calc
    _ = ∑ k : Fin I.card,
        condMutualInfo (fun t => Φ (e k) (z t))
          (wordAt (walkLetters z R hstep) (2 ^ l (e k)))
          (fun t => maskedPriorHom K Φ (Finset.univ.filter (fun j : I => j.val < (e k).val)) (z t)) μ /
          (2 ^ l (e k) : ℕ) :=
      (Fintype.sum_equiv e.toEquiv _ _ (fun _ => rfl)).symm
    _ = ∑ k : Fin I.card, H k.val := by
      apply Finset.sum_congr rfl
      intro k _
      have hw := congrArg (fun L : ℕ =>
        condMutualInfo (fun t => φ k.val (z t)) (wordAt (walkLetters z R hstep) (2 ^ L))
          (observationHistory (fun j t => φ j (z t)) k.val) μ)
        (finiteClampedLevel_get (fun k => l (e k)) k)
      dsimp only [H]
      rw [hw]
      dsimp only [level]
      simp only [finiteClampedLevel_get]
      exact congrArg (fun r : ℝ => r / (2 ^ l (e k) : ℕ))
        (countable_selectedFamilyBatch_history_information I K Φ μ z _ k)
    _ = ∑ n ∈ Finset.range I.card, H n := Fin.sum_univ_eq_sum_range H I.card
    _ = ∑ n ∈ Finset.range (I.card + 1), H n := by rw [Finset.sum_range_succ, hz, add_zero]

/-- The common smoothed walk upper budget instantiated with actual sorted
family maps and their clamped dyadic levels. -/
theorem smoothedTimeLaw_selectedFamily_dyadic_budget
    {Ω : Type*} [Fintype Ω] [MeasurableSpace Ω] [MeasurableSingletonClass Ω]
    [MeasurableSpace Bool] [MeasurableSingletonClass Bool]
    (I : Finset ℕ) (K : I → Type*) [∀ i, AddCommGroup (K i)] [∀ i, Fintype (K i)]
    [∀ i, MeasurableSpace (K i)] [∀ i, MeasurableSingletonClass (K i)]
    (Φ : ∀ i, Point →+ K i) (μ : Measure Ω) [IsProbabilityMeasure μ] (b : Ω → ℕ)
    (z : ℕ → Point) (R : ℕ) (hstep : ∀ t, sqDist (z (t + 1)) (z t) ≤ (R : ℤ))
    (l : I → ℕ) (hl : Monotone (fun k => l (selectedFamilyOrder I k)))
    (T : ℝ) (hT : 1 ≤ T) (hlength : ∀ i, ((2 ^ l i : ℕ) : ℝ) ≤ T) :
    (∑ i : I,
      condMutualInfo (fun t => Φ i (z t)) (wordAt (walkLetters z R hstep) (2 ^ l i))
        (fun t => maskedPriorHom K Φ (Finset.univ.filter (fun j : I => j.val < i.val)) (z t))
          (smoothedTimeLaw μ b (terminalSmoothingLength T)) / (2 ^ l i : ℕ)) ≤
      2 * Real.log (2 * (R + 1) + 1 : ℕ) +
        I.card * ((1 + 9 * Real.log T + 2 * Real.log (2 * (R + 1) + 1 : ℕ)) / T ^ 9) := by
  let : NeZero (terminalSmoothingLength T) := ⟨(terminalSmoothingLength_pos T).ne'⟩
  rw [selectedFamily_dyadic_information_sum]
  exact smoothedTimeLaw_walk_dyadic_budget μ b z R hstep _ _
    (finiteClampedLevel_mono _ hl) I.card T hT
    (finiteClampedLevel_word_bound _ T hT (fun k => hlength _) I.card)

end BinaryFormMoat.EntropyIntegration
#print axioms BinaryFormMoat.EntropyIntegration.selectedFamily_dyadic_information_sum
#print axioms BinaryFormMoat.EntropyIntegration.smoothedTimeLaw_selectedFamily_dyadic_budget
