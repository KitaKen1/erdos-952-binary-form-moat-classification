import Integrations.PairedWalkTerminalRestart435

noncomputable section
namespace BinaryFormMoat.GeometryIntegration
open EntropyIntegration MeasureTheory ProbabilityTheory
variable {A : Type*} [Fintype A] [MeasurableSpace A] [MeasurableSingletonClass A]

/-- The actual marginal at global index q, retaining every past coordinate. -/
def pairedWalkPrefixLaw (z : ℕ → Point) (N : ℕ → ℕ) (b : A → ℕ)
    (k q : ℕ) (hkq : k ≤ q) (ν : Measure (PairedWalkSource A N k)) :
    Measure (PairedWalkSource A N q) :=
  (pairedWalkTailLaw z N b k ν (q - k)).map
    (pairedWalkCast N (k + (q - k)) q (by omega))

instance pairedWalkPrefixLaw_isProbabilityMeasure (z : ℕ → Point) (N : ℕ → ℕ) (b : A → ℕ)
    (k q : ℕ) (hkq : k ≤ q) (ν : Measure (PairedWalkSource A N k)) [IsProbabilityMeasure ν] :
    IsProbabilityMeasure (pairedWalkPrefixLaw z N b k q hkq ν) := by
  unfold pairedWalkPrefixLaw
  infer_instance

/-- Global-index form of conditional restart: the original raw checkpoint time,
its original positive event and the SAME terminal offset are preserved. -/
theorem pairedWalkTailTerminalTime_cond_restart_at_identDistrib (z : ℕ → Point) (N : ℕ → ℕ)
    (b : A → ℕ) (k q n : ℕ) (hkq : k ≤ q) (hqn : q ≤ n)
    (ν : Measure (PairedWalkSource A N k)) [IsProbabilityMeasure ν] (L : ℕ) [NeZero L] (c : ℕ) :
    IdentDistrib (pairedWalkTailTerminalTime N b k (n - k) L)
      (pairedWalkTailTerminalTime N b q (n - q) L)
      ((pairedWalkTailTerminalLaw z N b k ν (n - k) L)[|
        (fun ω => pairedWalkTime N b (k + (q - k))
          (pairedWalkTailCheckpoint N k (n - k) L (q - k) (Nat.sub_le_sub_right hqn k) ω)) ⁻¹' {c}])
      (pairedWalkTailTerminalLaw z N b q ((pairedWalkPrefixLaw z N b k q hkq ν)[|
        pairedWalkTime N b q ⁻¹' {c}]) (n - q) L) := by
  obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le hkq
  obtain ⟨r, rfl⟩ := Nat.exists_eq_add_of_le hqn
  have transport (a s v : ℕ) (ha : a = j) (hs : s = j + r) (hv : v = r) :
      IdentDistrib (pairedWalkTailTerminalTime N b k s L)
        (pairedWalkTailTerminalTime N b (k + j) v L)
        ((pairedWalkTailTerminalLaw z N b k ν s L)[|
          (fun ω => pairedWalkTime N b (k + a)
            (pairedWalkTailCheckpoint N k s L a (by omega) ω)) ⁻¹' {c}])
        (pairedWalkTailTerminalLaw z N b (k + j)
          (((pairedWalkTailLaw z N b k ν a).map (pairedWalkCast N (k + a) (k + j) (by omega)))[|
            pairedWalkTime N b (k + j) ⁻¹' {c}]) v L) := by
    subst a
    subst s
    subst v
    change IdentDistrib _ _ _ (pairedWalkTailTerminalLaw z N b (k + j)
      (((pairedWalkTailLaw z N b k ν j).map id)[|pairedWalkTime N b (k + j) ⁻¹' {c}]) r L)
    rw [Measure.map_id]
    exact pairedWalkTailTerminalTime_cond_restart_identDistrib z N b k ν j r L
      (pairedWalkTime N b (k + j)) c
  exact transport ((k + j) - k) (((k + j) + r) - k) (((k + j) + r) - (k + j))
    (by omega) (by omega) (by omega)

/-- The original terminal-source checkpoint fiber has the exact marginal mass.
Thus positivity transfers to the fresh starting conditional probability law. -/
theorem pairedWalkTailTerminalLaw_prefix_time_mass (z : ℕ → Point) (N : ℕ → ℕ)
    (b : A → ℕ) (k q n : ℕ) (hkq : k ≤ q) (hqn : q ≤ n)
    (ν : Measure (PairedWalkSource A N k)) (L : ℕ) [NeZero L] (c : ℕ) :
    pairedWalkTailTerminalLaw z N b k ν (n - k) L
      ((fun ω => pairedWalkTime N b (k + (q - k))
        (pairedWalkTailCheckpoint N k (n - k) L (q - k) (Nat.sub_le_sub_right hqn k) ω)) ⁻¹' {c}) =
      pairedWalkPrefixLaw z N b k q hkq ν (pairedWalkTime N b q ⁻¹' {c}) := by
  unfold pairedWalkPrefixLaw
  rw [Measure.map_apply (measurable_of_finite _)
    ((measurable_of_finite (pairedWalkTime N b q)) (MeasurableSet.singleton c))]
  have he : (pairedWalkCast N (k + (q - k)) q (by omega)) ⁻¹'
      (pairedWalkTime N b q ⁻¹' {c}) = pairedWalkTime N b (k + (q - k)) ⁻¹' {c} := by
    ext ω
    simp only [Set.mem_preimage, Set.mem_singleton_iff, pairedWalkCast_time]
  rw [he]
  change pairedWalkTailTerminalLaw z N b k ν (n - k) L
    ((pairedWalkTailCheckpoint N k (n - k) L (q - k) _) ⁻¹'
      (pairedWalkTime N b (k + (q - k)) ⁻¹' {c})) = _
  rw [← Measure.map_apply (measurable_of_finite _)
    ((measurable_of_finite (pairedWalkTime N b (k + (q - k)))) (MeasurableSet.singleton c)),
    pairedWalkTailTerminalLaw_checkpoint_map]

end BinaryFormMoat.GeometryIntegration
#print axioms BinaryFormMoat.GeometryIntegration.pairedWalkPrefixLaw
#print axioms BinaryFormMoat.GeometryIntegration.pairedWalkPrefixLaw_isProbabilityMeasure
#print axioms BinaryFormMoat.GeometryIntegration.pairedWalkTailTerminalTime_cond_restart_at_identDistrib
#print axioms BinaryFormMoat.GeometryIntegration.pairedWalkTailTerminalLaw_prefix_time_mass
