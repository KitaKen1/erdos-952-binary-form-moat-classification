import Integrations.PosteriorRootPassing435
import Integrations.CommonPassingQuota435

noncomputable section
open scoped Classical
namespace BinaryFormMoat.EntropyIntegration
open MeasureTheory ProbabilityTheory
attribute [local irreducible] paperPassingCount

/-- Expected list cardinality for a constructed finite independent package law. -/
def independentPassingListMean {C H : Type*} [Fintype C] [MeasurableSpace H]
    (ν : Measure H) (m : ℕ) (reject : C → H → Prop) : ℝ :=
  ∫ h : Fin m → H, ((passingList reject h).card : ℝ)
    ∂Measure.pi (fun _ : Fin m => ν)

set_option maxHeartbeats 800000 in
/-- Actual posterior source packages and ONE dyadic-batch quota yield the
5*p^(1-beta) list bound. Candidate exceptions and hit floors are derived. -/
theorem favorable_root_expected_passingList
    {Ω A D : Type*} [Fintype Ω] [MeasurableSpace Ω] [MeasurableSingletonClass Ω]
    [Fintype A] [MeasurableSpace A] [MeasurableSingletonClass A]
    [Fintype D] [MeasurableSpace D] [MeasurableSingletonClass D]
    (ν : Measure Ω) [IsProbabilityMeasure ν] (σ : Ω → A) (b : Ω → ℕ)
    (N : ℕ) [NeZero N] (F : A → D) (d : D)
    (hd : (ν.prod (uniformOn (Set.univ : Set (Fin N)))) ((fun ω => F (σ ω.1)) ⁻¹' {d}) ≠ 0)
    (f : Polynomial ℤ) (hf : Irreducible f) (hdeg : 2 ≤ f.natDegree)
    (p : ℕ) [NeZero p] (ρ : ZMod p) (hρ : f.eval₂ (Int.castRingHom (ZMod p)) ρ = 0)
    (z : ℕ → Point) (hz : Function.Injective z) (R : ℕ)
    (hstep : ∀ t, sqDist (z (t + 1)) (z t) ≤ (R : ℤ))
    (Y : A → ZMod p) (T L : ℕ) (hT : 2 ≤ T) (hL : 1 ≤ L) (hlo : T ≤ p) (hhi : p ≤ 2 * T)
    (hsmall : coefficientBound f f.natDegree * ((R + 1) * L) ^ f.natDegree < p)
    (τ β : ℝ) (hτ : 0 < τ) (hβ : 0 ≤ β) (herr : (L : ℝ) / N ≤ (τ / p) / 2)
    (hbad : fiberConditionalReal (ν.prod (uniformOn (Set.univ : Set (Fin N))))
      (fun ω => F (σ ω.1)) d
      {ω | (p : ℝ) ^ (1 - β) ≤ ((lowProbabilityResidues
        ((ν.prod (uniformOn (Set.univ : Set (Fin N))))[|
          (fun ω => σ ω.1) ⁻¹' {σ ω.1}])
        (fun ω => rootResidueHom p ρ (z (b ω.1 + ω.2.val))) τ).card : ℝ)} ≤ (1 : ℝ) / 2) :
    independentPassingListMean
      ((ν.prod (uniformOn (Set.univ : Set (Fin N))))[|(fun ω => F (σ ω.1)) ⁻¹' {d}])
      (paperPassingCount T L τ β)
      (fun x ω => ω ∈ wordHitSet (fun t => rootResidueHom p ρ (z t))
        (fun ω => b ω.1 + ω.2.val) (fun ω => Y (σ ω.1) - x) L) ≤
      5 * (p : ℝ) ^ (1 - β) := by
  obtain ⟨B, hB, hfloor⟩ := favorable_root_candidate_rejection ν σ b N F d hd f hf hdeg
    p ρ hρ z hz R hstep Y L hsmall τ β hτ.le herr hbad
  let : IsProbabilityMeasure ((ν.prod (uniformOn (Set.univ : Set (Fin N))))[|
    (fun ω => F (σ ω.1)) ⁻¹' {d}]) := cond_isProbabilityMeasure hd
  let reject := fun (x : ZMod p) (ω : Ω × Fin N) =>
    ω ∈ wordHitSet (fun t => rootResidueHom p ρ (z t))
      (fun ω => b ω.1 + ω.2.val) (fun ω => Y (σ ω.1) - x) L
  have hfloor' : ∀ x ∉ B, (L : ℝ) * (τ / p) / 8 ≤
      ((ν.prod (uniformOn (Set.univ : Set (Fin N))))[|
        (fun ω => F (σ ω.1)) ⁻¹' {d}]).real {ω | reject x ω} := by
    intro x hx
    simpa only [reject, fiberConditionalReal, Set.ofPred_mem_eq] using hfloor x hx
  unfold independentPassingListMean
  exact expected_passingList_common_quota
    ((ν.prod (uniformOn (Set.univ : Set (Fin N))))[|(fun ω => F (σ ω.1)) ⁻¹' {d}])
    T L p hT hL hlo hhi τ β hτ hβ
    reject B hB hfloor'

/-- On a zero-avoiding walk the ORIGINAL checkpoint candidate cannot be
rejected by its own relative word. -/
theorem relative_word_true_candidate_not_rejected {Ω G : Type*} [AddGroup G]
    (V : ℕ → G) (u : Ω → ℕ) (Y : Ω → G) (L : ℕ) (ω : Ω)
    (hzero : ∀ t, V t ≠ 0) :
    ω ∉ wordHitSet V u (fun ω => Y ω - Y ω) L := by
  intro h
  simp only [wordHitSet, Set.mem_iUnion, wordHitEvent, Set.mem_ofPred_eq, sub_self] at h
  obtain ⟨i, hi⟩ := h
  exact hzero _ hi

/-- The common true residue survives every package sharing those checkpoint
data. Faithfulness of actual posterior data must still be instantiated. -/
theorem relative_word_true_candidate_in_list {Ω G J : Type*} [Fintype G] [AddGroup G] [Fintype J]
    (V : ℕ → G) (u : Ω → ℕ) (Y : Ω → G) (L : ℕ) (h : J → Ω) (x : G)
    (hzero : ∀ t, V t ≠ 0) (hY : ∀ j, Y (h j) = x) :
    x ∈ passingList (fun x ω => ω ∈ wordHitSet V u (fun ω => Y ω - x) L) h := by
  apply (mem_passingList _ h x).mpr
  intro j hj
  simp only [wordHitSet, Set.mem_iUnion, wordHitEvent, Set.mem_ofPred_eq] at hj
  obtain ⟨i, hi⟩ := hj
  rw [hY j, sub_self] at hi
  exact hzero _ hi

/-- The relative rejection test depends only on checkpoint-to-terminal
displacement and terminal-word prefix displacements, not hidden residues. -/
theorem relative_root_word_hit_iff_displacements {Ω : Type*} (p : ℕ) (ρ : ZMod p)
    (z : ℕ → Point) (t u : Ω → ℕ) (L : ℕ) (x : ZMod p) (ω : Ω) :
    ω ∈ wordHitSet (fun a => rootResidueHom p ρ (z a)) u
      (fun ω => rootResidueHom p ρ (z (t ω)) - x) L ↔
      ∃ i : Fin L, x + rootResidueHom p ρ (z (u ω) - z (t ω)) +
        rootResidueHom p ρ (z (u ω + i) - z (u ω)) = 0 := by
  simp only [wordHitSet, Set.mem_iUnion, wordHitEvent, Set.mem_ofPred_eq, map_sub]
  apply exists_congr
  intro i
  constructor
  · intro h
    rw [h]
    abel
  · intro h
    calc
      _ = (x + (rootResidueHom p ρ (z (u ω)) - rootResidueHom p ρ (z (t ω))) +
        (rootResidueHom p ρ (z (u ω + i)) - rootResidueHom p ρ (z (u ω)))) +
          (rootResidueHom p ρ (z (t ω)) - x) := by abel
      _ = _ := by rw [h, zero_add]

end BinaryFormMoat.EntropyIntegration
#print axioms BinaryFormMoat.EntropyIntegration.independentPassingListMean
#print axioms BinaryFormMoat.EntropyIntegration.favorable_root_expected_passingList
#print axioms BinaryFormMoat.EntropyIntegration.relative_word_true_candidate_not_rejected
#print axioms BinaryFormMoat.EntropyIntegration.relative_word_true_candidate_in_list
#print axioms BinaryFormMoat.EntropyIntegration.relative_root_word_hit_iff_displacements
