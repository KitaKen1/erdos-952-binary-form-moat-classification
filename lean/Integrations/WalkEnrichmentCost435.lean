import Integrations.WalkRetainedEntropy435
import Integrations.WalkDisplacement435

noncomputable section

namespace BinaryFormMoat.GeometryIntegration
open EntropyIntegration MeasureTheory ProbabilityTheory

/-- The endpoints may be in either time order inside the SAME forward window. -/
theorem two_window_endpoints_displacement_mem (z : ℕ → Point) (D N : ℕ)
    (hstep : ∀ t, |(z (t + 1)).1 - (z t).1| ≤ D ∧
      |(z (t + 1)).2 - (z t).2| ≤ D)
    (t u v : ℕ) (htu : t ≤ u) (hu : u ≤ t + N) (htv : t ≤ v) (hv : v ≤ t + N) :
    z u - z v ∈ displacementBox ((2 * D) * N) := by
  have hx := (mem_displacementBox _ _).mp (walk_displacement_mem z D hstep N t u htu hu)
  have hy := (mem_displacementBox _ _).mp (walk_displacement_mem z D hstep N t v htv hv)
  have he : (D * N : ℕ) + (D * N : ℤ) = ((2 * D) * N : ℕ) := by push_cast; ring
  apply (mem_displacementBox _ _).mpr
  constructor
  · have h := abs_sub_le (z u).1 (z t).1 (z v).1
    rw [abs_sub_comm (z t).1 (z v).1] at h
    exact (h.trans (add_le_add hx.1 hy.1)).trans_eq he
  · have h := abs_sub_le (z u).2 (z t).2 (z v).2
    rw [abs_sub_comm (z t).2 (z v).2] at h
    exact (h.trans (add_le_add hx.2 hy.2)).trans_eq he

section FiniteSource
variable {Ω : Type*} [Fintype Ω] [MeasurableSpace Ω] [MeasurableSingletonClass Ω]
  (μ : Measure Ω) [IsProbabilityMeasure μ]

omit [IsProbabilityMeasure μ] in
theorem point_entropy_le_displacementBox (B : ℕ) (X : Ω → Point)
    (hX : ∀ ω, X ω ∈ displacementBox B) :
    entropy X μ ≤ 2 * Real.log (2 * B + 1 : ℕ) := by
  have h := entropy_le_log_card_of_mem (A := displacementBox B) (measurable_of_finite X)
    (ae_of_all μ hX)
  simpa only [displacementBox_card, Nat.cast_pow, Real.log_pow, Nat.cast_ofNat] using h

omit [IsProbabilityMeasure μ] in
/-- Both physical losses use the original mixed-base law. A coarse constant
depending only on D replaces a fresh argument on every exact base fiber. -/
theorem walk_window_displacement_entropy_cost (z : ℕ → Point) (D N : ℕ)
    (hstep : ∀ t, |(z (t + 1)).1 - (z t).1| ≤ D ∧
      |(z (t + 1)).2 - (z t).2| ≤ D)
    (t u v : Ω → ℕ) (htu : ∀ ω, t ω ≤ u ω) (hu : ∀ ω, u ω ≤ t ω + N)
    (htv : ∀ ω, t ω ≤ v ω) (hv : ∀ ω, v ω ≤ t ω + N) :
    entropy (fun ω => z (u ω) - z (t ω)) μ + entropy (fun ω => z (u ω) - z (v ω)) μ ≤
      4 * Real.log (N + 1 : ℕ) + 4 * Real.log (4 * D + 1 : ℕ) := by
  have hx := point_entropy_le_displacementBox μ (D * N) (fun ω => z (u ω) - z (t ω))
    (fun ω => walk_displacement_mem z D hstep N (t ω) (u ω) (htu ω) (hu ω))
  have hy := point_entropy_le_displacementBox μ ((2 * D) * N) (fun ω => z (u ω) - z (v ω))
    (fun ω => two_window_endpoints_displacement_mem z D N hstep
      (t ω) (u ω) (v ω) (htu ω) (hu ω) (htv ω) (hv ω))
  have lx := displacement_log_bound D N
  have ly := displacement_log_bound (2 * D) N
  have he : 2 * (2 * D) + 1 = 4 * D + 1 := by ring
  rw [he] at ly
  have hl : Real.log (2 * D + 1 : ℕ) ≤ Real.log (4 * D + 1 : ℕ) :=
    Real.log_le_log (by positivity) (by exact_mod_cast (by omega : 2 * D + 1 ≤ 4 * D + 1))
  linarith

section Residues
variable {ι : Type*} [Fintype ι] [DecidableEq ι] (K : ι → Type*)
  [∀ i, AddCommGroup (K i)] [∀ i, Fintype (K i)]
  [∀ i, MeasurableSpace (K i)] [∀ i, MeasurableSingletonClass (K i)]
  (F : ∀ i, Point →+ K i)

theorem walk_window_retained_enrichment_budget (S : Finset ι) (z : ℕ → Point) (D N : ℕ)
    (hstep : ∀ t, |(z (t + 1)).1 - (z t).1| ≤ D ∧
      |(z (t + 1)).2 - (z t).2| ≤ D)
    (t u v : Ω → ℕ) (htu : ∀ ω, t ω ≤ u ω) (hu : ∀ ω, u ω ≤ t ω + N)
    (htv : ∀ ω, t ω ≤ v ω) (hv : ∀ ω, v ω ≤ t ω + N) (κ : ℝ)
    (hκ : κ ≤ ∑ i ∈ Finset.univ \ S, condEntropy (fun ω => F i (z (u ω) - z (v ω)))
      (fun ω => (residuePrefix K F S (fun ω => z (u ω)) ω,
        residuePrefix K F S (fun ω => z (v ω)) ω)) μ) :
    κ + entropy (fun ω i => F i (z (t ω))) μ -
      4 * Real.log (N + 1 : ℕ) - 4 * Real.log (4 * D + 1 : ℕ) -
      2 * (∑ i ∈ S, Real.log (Fintype.card (K i) : ℝ)) ≤
    ∑ i ∈ Finset.univ \ S,
      (condEntropy (fun ω => F i (z (u ω))) (residuePrefix K F S (fun ω => z (u ω))) μ +
       condEntropy (fun ω => F i (z (v ω))) (residuePrefix K F S (fun ω => z (v ω))) μ) := by
  have h := walk_residue_retained_enrichment_budget K μ F S
    (fun ω => z (u ω)) (fun ω => z (v ω)) (fun ω => z (t ω)) κ hκ
  have hc := walk_window_displacement_entropy_cost μ z D N hstep t u v htu hu htv hv
  linarith

/-- The actual prefix alphabets and finite window provide all error terms;
only the geometric coordinate floor kappa remains an input to this budget. -/
theorem walk_window_retained_enrichment_numeric_budget (S : Finset ι) (z : ℕ → Point) (D N : ℕ)
    (hstep : ∀ t, |(z (t + 1)).1 - (z t).1| ≤ D ∧
      |(z (t + 1)).2 - (z t).2| ≤ D)
    (t u v : Ω → ℕ) (htu : ∀ ω, t ω ≤ u ω) (hu : ∀ ω, u ω ≤ t ω + N)
    (htv : ∀ ω, t ω ≤ v ω) (hv : ∀ ω, v ω ≤ t ω + N) (κ L : ℝ)
    (hN : Real.log (N + 1 : ℕ) ≤ L) (T : ℕ)
    (hcard : ∀ i ∈ S, Fintype.card (K i) ≤ 2 * T)
    (hκ : κ ≤ ∑ i ∈ Finset.univ \ S, condEntropy (fun ω => F i (z (u ω) - z (v ω)))
      (fun ω => (residuePrefix K F S (fun ω => z (u ω)) ω,
        residuePrefix K F S (fun ω => z (v ω)) ω)) μ) :
    κ + entropy (fun ω i => F i (z (t ω))) μ - 4 * L -
      4 * Real.log (4 * D + 1 : ℕ) - 2 * (S.card : ℝ) * Real.log (2 * T : ℕ) ≤
    ∑ i ∈ Finset.univ \ S,
      (condEntropy (fun ω => F i (z (u ω))) (residuePrefix K F S (fun ω => z (u ω))) μ +
       condEntropy (fun ω => F i (z (v ω))) (residuePrefix K F S (fun ω => z (v ω))) μ) := by
  have h := walk_window_retained_enrichment_budget μ K F S z D N hstep t u v htu hu htv hv κ hκ
  have hb : (∑ i ∈ S, Real.log (Fintype.card (K i) : ℝ)) ≤
      (S.card : ℝ) * Real.log (2 * T : ℕ) := by
    calc
      _ ≤ ∑ _i ∈ S, Real.log (2 * T : ℕ) := by
        apply Finset.sum_le_sum
        intro i hi
        exact Real.log_le_log (by exact_mod_cast (Fintype.card_pos : 0 < Fintype.card (K i)))
          (by exact_mod_cast hcard i hi)
      _ = _ := by simp
  linarith

end Residues
end FiniteSource
end BinaryFormMoat.GeometryIntegration

#print axioms BinaryFormMoat.GeometryIntegration.two_window_endpoints_displacement_mem
#print axioms BinaryFormMoat.GeometryIntegration.point_entropy_le_displacementBox
#print axioms BinaryFormMoat.GeometryIntegration.walk_window_displacement_entropy_cost
#print axioms BinaryFormMoat.GeometryIntegration.walk_window_retained_enrichment_budget
#print axioms BinaryFormMoat.GeometryIntegration.walk_window_retained_enrichment_numeric_budget
