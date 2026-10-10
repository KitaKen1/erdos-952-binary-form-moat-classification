import Integrations.PairedWalkProcess435

noncomputable section
namespace BinaryFormMoat.GeometryIntegration
open EntropyIntegration MeasureTheory ProbabilityTheory

/-- Read the exact history before r more transitions, retaining every coordinate. -/
def pairedWalkPast {A : Type*} (N : ℕ → ℕ) (k : ℕ) :
    (r : ℕ) → PairedWalkSource A N (k + r) → PairedWalkSource A N k
  | 0 => id
  | r + 1 => fun ω => pairedWalkPast N k r ω.1.1

theorem pairedWalkPast_origin {A : Type*} (N : ℕ → ℕ) (k r : ℕ)
    (ω : PairedWalkSource A N (k + r)) :
    pairedWalkOrigin N k (pairedWalkPast N k r ω) = pairedWalkOrigin N (k + r) ω := by
  induction r with
  | zero => rfl
  | succ r ih => exact ih ω.1.1

/-- The actual time at an earlier history is below the later time, and the
advance is bounded by precisely the intervening windows. -/
theorem pairedWalkPast_time_bounds {A : Type*} (N : ℕ → ℕ) (b : A → ℕ) (k r : ℕ)
    (ω : PairedWalkSource A N (k + r)) :
    pairedWalkTime N b k (pairedWalkPast N k r ω) ≤ pairedWalkTime N b (k + r) ω ∧
      pairedWalkTime N b (k + r) ω ≤ pairedWalkTime N b k (pairedWalkPast N k r ω) +
        ∑ j ∈ Finset.range r, N (k + j) := by
  induction r with
  | zero => simp [pairedWalkPast]
  | succ r ih =>
    have ht := pairedWalkTime_step_bounds N b (k + r) ω
    have hi := ih ω.1.1
    constructor
    · exact hi.1.trans ht.1
    · change pairedWalkTime N b (k + r + 1) ω ≤
        pairedWalkTime N b k (pairedWalkPast N k r ω.1.1) +
          ∑ j ∈ Finset.range (r + 1), N (k + j)
      rw [Finset.sum_range_succ]
      exact ht.2.trans (by omega)

/-- Every earlier complete history has EXACTLY its original law on the common
later source. This is not conditioning on its final time or residue. -/
theorem pairedWalkPast_law_map {A : Type*} [Fintype A] [MeasurableSpace A]
    [MeasurableSingletonClass A] (z : ℕ → Point) (N : ℕ → ℕ)
    (μ : Measure A) (b : A → ℕ) (k r : ℕ) :
    (pairedWalkLaw z N μ b (k + r)).map (pairedWalkPast N k r) = pairedWalkLaw z N μ b k := by
  induction r with
  | zero => exact Measure.map_id
  | succ r ih =>
    change (pairedWalkLaw z N μ b (k + r + 1)).map
      (pairedWalkPast N k r ∘ (fun ω => ω.1.1)) = _
    rw [← Measure.map_map (measurable_of_finite _) (measurable_of_finite _),
      pairedWalkLaw_previous_map, ih]

/-- A checkpoint reader on ONE full history source, including the terminal
checkpoint k=n. The cast only reconciles n=k+(n-k). -/
def pairedWalkCheckpoint {A : Type*} (N : ℕ → ℕ) (n : ℕ) (k : Fin (n + 1)) :
    PairedWalkSource A N n → PairedWalkSource A N k.val := fun ω =>
  pairedWalkPast N k.val (n - k.val)
    (cast (congrArg (PairedWalkSource A N) (by omega : n = k.val + (n - k.val))) ω)

theorem pairedWalkCheckpoint_add {A : Type*} (N : ℕ → ℕ) (k r : ℕ)
    (hk : k < k + r + 1) :
    pairedWalkCheckpoint (A := A) N (k + r) ⟨k, hk⟩ = pairedWalkPast N k r := by
  funext ω
  dsimp [pairedWalkCheckpoint]
  have h : k + r - k = r := Nat.add_sub_cancel_left k r
  have transport (a c : ℕ) (h : a = c)
      (ω : PairedWalkSource A N (k + c))
      (hc : k + c = k + a) :
      pairedWalkPast N k a (cast (congrArg (PairedWalkSource A N) hc) ω) =
        pairedWalkPast N k c ω := by
    subst a
    rfl
  exact transport _ _ h ω (by omega)

theorem pairedWalkCheckpoint_origin {A : Type*} (N : ℕ → ℕ) (n : ℕ) (k : Fin (n + 1))
    (ω : PairedWalkSource A N n) :
    pairedWalkOrigin N k.val (pairedWalkCheckpoint N n k ω) = pairedWalkOrigin N n ω := by
  rcases k with ⟨k, hk⟩
  obtain ⟨r, rfl⟩ := Nat.exists_eq_add_of_le (by omega : k ≤ n)
  rw [pairedWalkCheckpoint_add]
  exact pairedWalkPast_origin N k r ω

theorem pairedWalkCheckpoint_time_bounds {A : Type*} (N : ℕ → ℕ) (b : A → ℕ)
    (n : ℕ) (k : Fin (n + 1)) (ω : PairedWalkSource A N n) :
    pairedWalkTime N b k.val (pairedWalkCheckpoint N n k ω) ≤ pairedWalkTime N b n ω ∧
      pairedWalkTime N b n ω ≤ pairedWalkTime N b k.val (pairedWalkCheckpoint N n k ω) +
        ∑ j ∈ Finset.range (n - k.val), N (k.val + j) := by
  rcases k with ⟨k, hk⟩
  obtain ⟨r, rfl⟩ := Nat.exists_eq_add_of_le (by omega : k ≤ n)
  rw [pairedWalkCheckpoint_add]
  simpa only [Nat.add_sub_cancel_left] using pairedWalkPast_time_bounds N b k r ω

theorem pairedWalkCheckpoint_law_map {A : Type*} [Fintype A] [MeasurableSpace A]
    [MeasurableSingletonClass A] (z : ℕ → Point) (N : ℕ → ℕ)
    (μ : Measure A) (b : A → ℕ) (n : ℕ) (k : Fin (n + 1)) :
    (pairedWalkLaw z N μ b n).map (pairedWalkCheckpoint N n k) = pairedWalkLaw z N μ b k.val := by
  rcases k with ⟨k, hk⟩
  obtain ⟨r, rfl⟩ := Nat.exists_eq_add_of_le (by omega : k ≤ n)
  rw [pairedWalkCheckpoint_add]
  exact pairedWalkPast_law_map z N μ b k r

end BinaryFormMoat.GeometryIntegration

#print axioms BinaryFormMoat.GeometryIntegration.pairedWalkPast
#print axioms BinaryFormMoat.GeometryIntegration.pairedWalkPast_origin
#print axioms BinaryFormMoat.GeometryIntegration.pairedWalkPast_time_bounds
#print axioms BinaryFormMoat.GeometryIntegration.pairedWalkPast_law_map
#print axioms BinaryFormMoat.GeometryIntegration.pairedWalkCheckpoint
#print axioms BinaryFormMoat.GeometryIntegration.pairedWalkCheckpoint_add
#print axioms BinaryFormMoat.GeometryIntegration.pairedWalkCheckpoint_origin
#print axioms BinaryFormMoat.GeometryIntegration.pairedWalkCheckpoint_time_bounds
#print axioms BinaryFormMoat.GeometryIntegration.pairedWalkCheckpoint_law_map
