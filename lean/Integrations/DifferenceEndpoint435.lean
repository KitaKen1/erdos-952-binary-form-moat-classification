import Integrations.UniformDifferenceEntropy435
import Mathlib.MeasureTheory.Integral.Prod

noncomputable section

namespace BinaryFormMoat.GeometryIntegration
open EntropyIntegration MeasureTheory ProbabilityTheory

abbrev WalkDifferences (z : ℕ → Point) (N : ℕ) :=
  ↥(pointDifferences (walkVertexSet z N))

instance walkDifferences_nonempty (z : ℕ → Point) (N : ℕ) : Nonempty (WalkDifferences z N) := by
  refine ⟨⟨0, (mem_pointDifferences _ _).mpr ?_⟩⟩
  exact ⟨z 0, mem_walkVertexSet z N 0 (Nat.zero_le _),
    z 0, mem_walkVertexSet z N 0 (Nat.zero_le _), sub_self _⟩

theorem exists_walkDifference_times (z : ℕ → Point) (N : ℕ) (h : WalkDifferences z N) :
    ∃ p : Fin (N + 1) × Fin (N + 1), z p.1.val - z p.2.val = h.val := by
  obtain ⟨a, ha, b, hb, he⟩ := (mem_pointDifferences _ _).mp h.property
  obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp ha
  obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hb
  exact ⟨(⟨i, Finset.mem_range.mp hi⟩, ⟨j, Finset.mem_range.mp hj⟩), he⟩

/-- One deterministic representing time pair for each distinct difference.
There is no prime/root parameter in this choice. -/
def walkDifferenceTimes (z : ℕ → Point) (N : ℕ) (h : WalkDifferences z N) :
    Fin (N + 1) × Fin (N + 1) :=
  Classical.choose (exists_walkDifference_times z N h)

theorem walkDifferenceTimes_spec (z : ℕ → Point) (N : ℕ) (h : WalkDifferences z N) :
    z (walkDifferenceTimes z N h).1.val - z (walkDifferenceTimes z N h).2.val = h.val :=
  Classical.choose_spec (exists_walkDifference_times z N h)

def differenceEndpointIndex (z : ℕ → Point) (N : ℕ)
    (s : WalkDifferences z N × Bool) : Fin (N + 1) :=
  if s.2 then (walkDifferenceTimes z N s.1).1 else (walkDifferenceTimes z N s.1).2

def differenceEndpointSourceLaw (z : ℕ → Point) (N : ℕ) :
    Measure (WalkDifferences z N × Bool) :=
  (uniformOn (Set.univ : Set (WalkDifferences z N))).prod (uniformOn (Set.univ : Set Bool))

instance differenceEndpointSourceLaw_isProbabilityMeasure (z : ℕ → Point) (N : ℕ) :
    IsProbabilityMeasure (differenceEndpointSourceLaw z N) := by
  unfold differenceEndpointSourceLaw
  infer_instance

theorem differenceEndpointSourceLaw_difference_map (z : ℕ → Point) (N : ℕ) :
    (differenceEndpointSourceLaw z N).map Prod.fst =
      uniformOn (Set.univ : Set (WalkDifferences z N)) := by
  rw [differenceEndpointSourceLaw, Measure.map_fst_prod]
  rw [measure_univ, one_smul]

theorem differenceEndpointSourceLaw_coin_map (z : ℕ → Point) (N : ℕ) :
    (differenceEndpointSourceLaw z N).map Prod.snd = uniformOn (Set.univ : Set Bool) := by
  rw [differenceEndpointSourceLaw, Measure.map_snd_prod]
  simp

theorem differenceEndpointSourceLaw_independent (z : ℕ → Point) (N : ℕ) :
    IndepFun (Prod.fst : WalkDifferences z N × Bool → WalkDifferences z N) Prod.snd
      (differenceEndpointSourceLaw z N) :=
  indepFun_prod measurable_id measurable_id

theorem differenceEndpointSourceLaw_coin_fair (z : ℕ → Point) (N : ℕ) (c : Bool) :
    (differenceEndpointSourceLaw z N).real (Prod.snd ⁻¹' {c}) = (1 : ℝ) / 2 := by
  rw [← map_measureReal_apply measurable_snd (MeasurableSet.singleton c),
    differenceEndpointSourceLaw_coin_map]
  rw [measureReal_def, uniformOn_univ]
  simp

theorem differenceEndpointIndex_bounds (z : ℕ → Point) (N t : ℕ)
    (s : WalkDifferences z N × Bool) :
    t ≤ t + (differenceEndpointIndex z N s).val ∧
      t + (differenceEndpointIndex z N s).val ≤ t + N := by
  have h := (differenceEndpointIndex z N s).isLt
  omega

/-- The endpoint test law is the average of the two representing endpoint
laws, while the underlying DIFFERENCE retains its uniform marginal. -/
theorem differenceEndpointSourceLaw_integral (z : ℕ → Point) (N : ℕ) (f : Point → ℝ) :
    ∫ s, f (z (differenceEndpointIndex z N s).val) ∂differenceEndpointSourceLaw z N =
      ((∫ h : WalkDifferences z N, f (z (walkDifferenceTimes z N h).1.val)
        ∂uniformOn (Set.univ : Set (WalkDifferences z N))) +
       (∫ h : WalkDifferences z N, f (z (walkDifferenceTimes z N h).2.val)
        ∂uniformOn (Set.univ : Set (WalkDifferences z N)))) / 2 := by
  rw [differenceEndpointSourceLaw, integral_prod _ Integrable.of_finite]
  have he : ∀ h : WalkDifferences z N,
      (∫ c : Bool, f (z (differenceEndpointIndex z N (h, c)).val)
        ∂uniformOn (Set.univ : Set Bool)) =
      (f (z (walkDifferenceTimes z N h).1.val) +
       f (z (walkDifferenceTimes z N h).2.val)) / 2 := by
    intro h
    rw [integral_fintype Integrable.of_finite, Fintype.sum_bool]
    simp only [measureReal_def, uniformOn_univ]
    simp [differenceEndpointIndex, smul_eq_mul]
    ring
  simp_rw [he]
  rw [integral_div, integral_add Integrable.of_finite Integrable.of_finite]

end BinaryFormMoat.GeometryIntegration

#print axioms BinaryFormMoat.GeometryIntegration.walkDifferences_nonempty
#print axioms BinaryFormMoat.GeometryIntegration.exists_walkDifference_times
#print axioms BinaryFormMoat.GeometryIntegration.walkDifferenceTimes_spec
#print axioms BinaryFormMoat.GeometryIntegration.differenceEndpointSourceLaw_isProbabilityMeasure
#print axioms BinaryFormMoat.GeometryIntegration.differenceEndpointSourceLaw_difference_map
#print axioms BinaryFormMoat.GeometryIntegration.differenceEndpointSourceLaw_coin_map
#print axioms BinaryFormMoat.GeometryIntegration.differenceEndpointSourceLaw_independent
#print axioms BinaryFormMoat.GeometryIntegration.differenceEndpointSourceLaw_coin_fair
#print axioms BinaryFormMoat.GeometryIntegration.differenceEndpointIndex_bounds
#print axioms BinaryFormMoat.GeometryIntegration.differenceEndpointSourceLaw_integral
