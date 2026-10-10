import Integrations.FinitePriorChain435
import Integrations.InformationHistory435

noncomputable section
open scoped Classical
namespace BinaryFormMoat.EntropyIntegration
open MeasureTheory ProbabilityTheory

/-- Mutual deterministic recovery preserves the conditioning experiment.
The recovery maps need not be injective on the full ambient alphabets. -/
theorem condMutualInfo_of_mutual_functions {Ω S T U V : Type*}
    [Fintype Ω] [MeasurableSpace Ω] [MeasurableSingletonClass Ω]
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
  have h₁ := condMutualInfo_of_inj (measurable_of_finite X) (measurable_of_finite Y)
    (measurable_of_finite Z) μ hif
  have h₂ := condMutualInfo_of_inj (measurable_of_finite X) (measurable_of_finite Y)
    (measurable_of_finite W) μ hig
  have he : ef ∘ Z = eg ∘ W := by funext ω; exact Prod.ext (hg ω).symm (hf ω)
  rw [← h₁, ← h₂, he]

/-- Exact newest-first indexing of the existing word-budget history. -/
theorem observationHistory_get {Ω T : Type*} (Y : ℕ → Ω → T) (ω : Ω) (n : ℕ)
    (i : Fin n) : observationHistory Y n ω i = Y (n - 1 - i.val) ω := by
  induction n with
  | zero => exact Fin.elim0 i
  | succ n ih =>
    refine Fin.cases ?_ (fun k => ?_) i
    · simp [observationHistory]
    · dsimp only [observationHistory]
      rw [Fin.cons_succ, ih]
      congr 1
      simp only [Fin.val_succ]
      omega

/-- Faithful single-coordinate embedding into one finite ambient group. -/
def familyCoordinateEmbed {ι : Type*} [DecidableEq ι] (K : ι → Type*)
    [∀ i, AddCommGroup (K i)] (i : ι) (x : K i) : (j : ι) → K j :=
  fun j => if h : j = i then h.symm ▸ x else 0

theorem familyCoordinateEmbed_self {ι : Type*} [DecidableEq ι] (K : ι → Type*)
    [∀ i, AddCommGroup (K i)] (i : ι) (x : K i) : familyCoordinateEmbed K i x i = x := by
  simp [familyCoordinateEmbed]

theorem familyCoordinateEmbed_injective {ι : Type*} [DecidableEq ι] (K : ι → Type*)
    [∀ i, AddCommGroup (K i)] (i : ι) : Function.Injective (familyCoordinateEmbed K i) := by
  intro x y h
  simpa only [familyCoordinateEmbed_self] using congrFun h i

def familyCoordinateHom {ι : Type*} [DecidableEq ι] (K : ι → Type*)
    [∀ i, AddCommGroup (K i)] (Φ : ∀ i, Point →+ K i) (i : ι) :
    Point →+ ((j : ι) → K j) where
  toFun x := familyCoordinateEmbed K i (Φ i x)
  map_zero' := by
    funext j
    by_cases h : j = i
    · subst j; simp [familyCoordinateEmbed]
    · simp [familyCoordinateEmbed, h]
  map_add' := by
    intro x y
    funext j
    by_cases h : j = i
    · subst j; simp [familyCoordinateEmbed]
    · simp [familyCoordinateEmbed, h]

/-- Total actual observation sequence with zero dummy coordinates after N. -/
def finiteFamilyBatchHom {N : ℕ} (K : Fin N → Type*) [∀ i, AddCommGroup (K i)]
    (Φ : ∀ i, Point →+ K i) (n : ℕ) : Point →+ ((i : Fin N) → K i) :=
  if h : n < N then familyCoordinateHom K Φ ⟨n, h⟩ else 0

def finiteFamilyPriorHom {N : ℕ} (K : Fin N → Type*) [∀ i, AddCommGroup (K i)]
    (Φ : ∀ i, Point →+ K i) (n : ℕ) : Point →+ ((i : Fin N) → K i) :=
  maskedPriorHom K Φ (Finset.univ.filter (fun i : Fin N => i.val < n))

def finiteFamilyPriorToHistory {N : ℕ} (K : Fin N → Type*) [∀ i, AddCommGroup (K i)]
    (n : ℕ) (hn : n ≤ N) (v : (i : Fin N) → K i) : Fin n → ((i : Fin N) → K i) :=
  fun k => familyCoordinateEmbed K ⟨n - 1 - k.val, by omega⟩ (v ⟨n - 1 - k.val, by omega⟩)

def finiteFamilyHistoryToPrior {N : ℕ} (K : Fin N → Type*) [∀ i, AddCommGroup (K i)]
    (n : ℕ) (v : Fin n → ((i : Fin N) → K i)) : (i : Fin N) → K i :=
  fun i => if h : i.val < n then v ⟨n - 1 - i.val, by omega⟩ i else 0

/-- Actual prefix data recover every earlier embedded observation. -/
theorem finiteFamilyPrior_recovers_history {Ω : Type*} {N : ℕ}
    (K : Fin N → Type*) [∀ i, AddCommGroup (K i)] (Φ : ∀ i, Point →+ K i)
    (X : Ω → Point) (n : ℕ) (hn : n ≤ N) (ω : Ω) :
    finiteFamilyPriorToHistory K n hn (finiteFamilyPriorHom K Φ n (X ω)) =
      observationHistory (fun k ω => finiteFamilyBatchHom K Φ k (X ω)) n ω := by
  funext k
  rw [observationHistory_get]
  have hk : n - 1 - k.val < N := by omega
  dsimp only [finiteFamilyPriorToHistory, finiteFamilyBatchHom]
  rw [dite_eq_left hk]
  change familyCoordinateEmbed K ⟨n - 1 - k.val, hk⟩
    (finiteFamilyPriorHom K Φ n (X ω) ⟨n - 1 - k.val, hk⟩) =
      familyCoordinateEmbed K ⟨n - 1 - k.val, hk⟩ (Φ ⟨n - 1 - k.val, hk⟩ (X ω))
  congr 1
  simp [finiteFamilyPriorHom, maskedPriorHom, show n - 1 - k.val < n by omega]

/-- The existing newest-first history recovers exactly the selected prefix. -/
theorem finiteFamilyHistory_recovers_prior {Ω : Type*} {N : ℕ}
    (K : Fin N → Type*) [∀ i, AddCommGroup (K i)] (Φ : ∀ i, Point →+ K i)
    (X : Ω → Point) (n : ℕ) (ω : Ω) :
    finiteFamilyHistoryToPrior K n
      (observationHistory (fun k ω => finiteFamilyBatchHom K Φ k (X ω)) n ω) =
        finiteFamilyPriorHom K Φ n (X ω) := by
  funext i
  by_cases hi : i.val < n
  · dsimp only [finiteFamilyHistoryToPrior]
    rw [dite_eq_left hi, observationHistory_get]
    have he : n - 1 - (n - 1 - i.val) = i.val := by omega
    rw [he]
    dsimp only [finiteFamilyBatchHom]
    rw [dite_eq_left i.isLt]
    change familyCoordinateEmbed K i (Φ i (X ω)) i = _
    rw [familyCoordinateEmbed_self]
    simp [finiteFamilyPriorHom, maskedPriorHom, hi]
  · simp [finiteFamilyHistoryToPrior, finiteFamilyPriorHom, maskedPriorHom, hi]

/-- The actual finite prefix prior and the existing observationHistory
condition EXACTLY the same information experiment, including n=0. -/
theorem finiteFamilyPrior_history_information {Ω S T : Type*} {N : ℕ}
    [Fintype Ω] [MeasurableSpace Ω] [MeasurableSingletonClass Ω]
    [Fintype S] [MeasurableSpace S] [MeasurableSingletonClass S]
    [Fintype T] [MeasurableSpace T] [MeasurableSingletonClass T]
    (K : Fin N → Type*) [∀ i, AddCommGroup (K i)] [∀ i, Fintype (K i)]
    [∀ i, MeasurableSpace (K i)] [∀ i, MeasurableSingletonClass (K i)]
    (Φ : ∀ i, Point →+ K i) (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : Ω → Point) (Y : Ω → S) (W : Ω → T) (n : ℕ) (hn : n ≤ N) :
    condMutualInfo Y W (fun ω => finiteFamilyPriorHom K Φ n (X ω)) μ =
      condMutualInfo Y W
        (observationHistory (fun k ω => finiteFamilyBatchHom K Φ k (X ω)) n) μ := by
  apply condMutualInfo_of_mutual_functions μ Y W _ _
    (finiteFamilyPriorToHistory K n hn) (finiteFamilyHistoryToPrior K n)
  · exact finiteFamilyPrior_recovers_history K Φ X n hn
  · exact finiteFamilyHistory_recovers_prior K Φ X n

end BinaryFormMoat.EntropyIntegration
#print axioms BinaryFormMoat.EntropyIntegration.condMutualInfo_of_mutual_functions
#print axioms BinaryFormMoat.EntropyIntegration.observationHistory_get
#print axioms BinaryFormMoat.EntropyIntegration.familyCoordinateEmbed
#print axioms BinaryFormMoat.EntropyIntegration.familyCoordinateEmbed_self
#print axioms BinaryFormMoat.EntropyIntegration.familyCoordinateEmbed_injective
#print axioms BinaryFormMoat.EntropyIntegration.familyCoordinateHom
#print axioms BinaryFormMoat.EntropyIntegration.finiteFamilyBatchHom
#print axioms BinaryFormMoat.EntropyIntegration.finiteFamilyPriorHom
#print axioms BinaryFormMoat.EntropyIntegration.finiteFamilyPriorToHistory
#print axioms BinaryFormMoat.EntropyIntegration.finiteFamilyHistoryToPrior
#print axioms BinaryFormMoat.EntropyIntegration.finiteFamilyPrior_recovers_history
#print axioms BinaryFormMoat.EntropyIntegration.finiteFamilyHistory_recovers_prior
#print axioms BinaryFormMoat.EntropyIntegration.finiteFamilyPrior_history_information
