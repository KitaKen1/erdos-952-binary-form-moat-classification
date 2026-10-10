import Integrations.SortedFamilyHistory435

noncomputable section
open scoped Classical
namespace BinaryFormMoat.EntropyIntegration
open MeasureTheory ProbabilityTheory

/-- Exact prior/target/history matching for the ACTUAL natural-time law,
whose source is countable rather than finite. -/
theorem countable_condMutualInfo_of_mutual_functions {Ω S T U V : Type*}
    [Countable Ω] [MeasurableSpace Ω] [MeasurableSingletonClass Ω]
    [Fintype S] [MeasurableSpace S] [MeasurableSingletonClass S]
    [Fintype T] [MeasurableSpace T] [MeasurableSingletonClass T]
    [Fintype U] [MeasurableSpace U] [MeasurableSingletonClass U]
    [Fintype V] [MeasurableSpace V] [MeasurableSingletonClass V]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (X : Ω → S) (Y : Ω → T)
    (Z : Ω → U) (W : Ω → V) (f : U → V) (g : V → U)
    (hf : ∀ ω, f (Z ω) = W ω) (hg : ∀ ω, g (W ω) = Z ω) :
    condMutualInfo X Y Z μ = condMutualInfo X Y W μ := by
  let ef : U → U × V := fun u => (u, f u)
  let eg : V → U × V := fun v => (g v, v)
  have hif : Function.Injective ef := fun _ _ h => congrArg Prod.fst h
  have hig : Function.Injective eg := fun _ _ h => congrArg Prod.snd h
  have h₁ := condMutualInfo_of_inj (measurable_of_countable X) (measurable_of_countable Y)
    (measurable_of_countable Z) μ hif
  have h₂ := condMutualInfo_of_inj (measurable_of_countable X) (measurable_of_countable Y)
    (measurable_of_countable W) μ hig
  have he : ef ∘ Z = eg ∘ W := by funext ω; exact Prod.ext (hg ω).symm (hf ω)
  rw [← h₁, ← h₂, he]

theorem countable_finiteFamilyPrior_history_information {Ω S T : Type*} {N : ℕ}
    [Countable Ω] [MeasurableSpace Ω] [MeasurableSingletonClass Ω]
    [Fintype S] [MeasurableSpace S] [MeasurableSingletonClass S]
    [Fintype T] [MeasurableSpace T] [MeasurableSingletonClass T]
    (K : Fin N → Type*) [∀ i, AddCommGroup (K i)] [∀ i, Fintype (K i)]
    [∀ i, MeasurableSpace (K i)] [∀ i, MeasurableSingletonClass (K i)]
    (Φ : ∀ i, Point →+ K i) (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : Ω → Point) (Y : Ω → S) (W : Ω → T) (n : ℕ) (hn : n ≤ N) :
    condMutualInfo Y W (fun ω => finiteFamilyPriorHom K Φ n (X ω)) μ =
      condMutualInfo Y W
        (observationHistory (fun k ω => finiteFamilyBatchHom K Φ k (X ω)) n) μ := by
  apply countable_condMutualInfo_of_mutual_functions μ Y W _ _
    (finiteFamilyPriorToHistory K n hn) (finiteFamilyHistoryToPrior K n)
  · exact finiteFamilyPrior_recovers_history K Φ X n hn
  · exact finiteFamilyHistory_recovers_prior K Φ X n

theorem countable_selectedFamilyPrior_history_information {Ω S T : Type*}
    [Countable Ω] [MeasurableSpace Ω] [MeasurableSingletonClass Ω]
    [Fintype S] [MeasurableSpace S] [MeasurableSingletonClass S]
    [Fintype T] [MeasurableSpace T] [MeasurableSingletonClass T]
    (I : Finset ℕ) (K : I → Type*) [∀ i, AddCommGroup (K i)] [∀ i, Fintype (K i)]
    [∀ i, MeasurableSpace (K i)] [∀ i, MeasurableSingletonClass (K i)]
    (Φ : ∀ i, Point →+ K i) (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : Ω → Point) (Y : Ω → S) (W : Ω → T) (j : I) :
    condMutualInfo Y W
      (fun ω => maskedPriorHom K Φ (Finset.univ.filter (fun i : I => i.val < j.val)) (X ω)) μ =
      condMutualInfo Y W
        (observationHistory (fun n ω => finiteFamilyBatchHom
          (fun k => K (selectedFamilyOrder I k)) (fun k => Φ (selectedFamilyOrder I k)) n (X ω))
          ((selectedFamilyOrder I).symm j).val) μ := by
  let e := selectedFamilyOrder I
  let ψ := fun ω => maskedPriorHom K Φ (Finset.univ.filter (fun i : I => i.val < j.val)) (X ω)
  have hi := condMutualInfo_of_inj (measurable_of_countable Y) (measurable_of_countable W)
    (measurable_of_countable ψ) μ (Equiv.piCongrLeft K e.toEquiv).symm.injective
  have he : (Equiv.piCongrLeft K e.toEquiv).symm ∘ ψ =
      fun ω => finiteFamilyPriorHom (fun k => K (e k)) (fun k => Φ (e k)) (e.symm j).val (X ω) := by
    funext ω
    exact selectedFamilyPrior_reindex I K Φ j (X ω)
  rw [he] at hi
  rw [← hi]
  exact countable_finiteFamilyPrior_history_information (fun k => K (e k)) (fun k => Φ (e k))
    μ X Y W (e.symm j).val (Nat.le_of_lt (e.symm j).isLt)

theorem countable_selectedFamilyBatch_history_information {Ω T : Type*}
    [Countable Ω] [MeasurableSpace Ω] [MeasurableSingletonClass Ω]
    [Fintype T] [MeasurableSpace T] [MeasurableSingletonClass T]
    (I : Finset ℕ) (K : I → Type*) [∀ i, AddCommGroup (K i)] [∀ i, Fintype (K i)]
    [∀ i, MeasurableSpace (K i)] [∀ i, MeasurableSingletonClass (K i)]
    (Φ : ∀ i, Point →+ K i) (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : Ω → Point) (W : Ω → T) (k : Fin I.card) :
    let e := selectedFamilyOrder I
    condMutualInfo (fun ω => Φ (e k) (X ω)) W
      (fun ω => maskedPriorHom K Φ (Finset.univ.filter (fun i : I => i.val < (e k).val)) (X ω)) μ =
      condMutualInfo
        (fun ω => finiteFamilyBatchHom (fun t => K (e t)) (fun t => Φ (e t)) k.val (X ω)) W
        (observationHistory (fun n ω => finiteFamilyBatchHom
          (fun t => K (e t)) (fun t => Φ (e t)) n (X ω)) k.val) μ := by
  dsimp only
  let e := selectedFamilyOrder I
  let K' := fun t => K (e t)
  let Y := fun ω => Φ (e k) (X ω)
  let Z := observationHistory (fun n ω => finiteFamilyBatchHom K' (fun t => Φ (e t)) n (X ω)) k.val
  have h := countable_selectedFamilyPrior_history_information I K Φ μ X Y W (e k)
  rw [show (selectedFamilyOrder I).symm (e k) = k from
    (selectedFamilyOrder I).symm_apply_apply k] at h
  rw [h]
  symm
  have hi := condMutualInfo_of_inj_map (μ := μ) (measurable_of_countable Y)
    (measurable_of_countable W) (measurable_of_countable Z)
    (fun _ => familyCoordinateEmbed K' k) (fun _ => familyCoordinateEmbed_injective K' k)
  simpa [finiteFamilyBatchHom, k.isLt, familyCoordinateHom, Y, Z] using hi

end BinaryFormMoat.EntropyIntegration
#print axioms BinaryFormMoat.EntropyIntegration.countable_condMutualInfo_of_mutual_functions
#print axioms BinaryFormMoat.EntropyIntegration.countable_finiteFamilyPrior_history_information
#print axioms BinaryFormMoat.EntropyIntegration.countable_selectedFamilyPrior_history_information
#print axioms BinaryFormMoat.EntropyIntegration.countable_selectedFamilyBatch_history_information
