import Integrations.PairedWalkRestart435

noncomputable section
namespace BinaryFormMoat.GeometryIntegration
open EntropyIntegration MeasureTheory ProbabilityTheory

/-- The history cast retains the SAME terminal smoothing coordinate. -/
def pairedWalkTerminalCast {A : Type*} (N : ℕ → ℕ) (n n' L : ℕ) (h : n = n') :
    PairedWalkSource A N n × Fin L → PairedWalkSource A N n' × Fin L :=
  Prod.map (pairedWalkCast N n n' h) id

theorem pairedWalkTerminalCast_time {A : Type*} (N : ℕ → ℕ) (b : A → ℕ)
    (k j r L : ℕ) (ω : PairedWalkTailTerminalSource A N k (j + r) L) :
    pairedWalkTailTerminalTime N b (k + j) r L
      (pairedWalkTerminalCast N (k + (j + r)) ((k + j) + r) L (Nat.add_assoc k j r).symm ω) =
        pairedWalkTailTerminalTime N b k (j + r) L ω := by
  dsimp only [pairedWalkTailTerminalTime, pairedWalkTerminalCast, Prod.map]
  rw [pairedWalkCast_time]
  rfl

theorem pairedWalkTerminalCast_checkpoint {A : Type*} (N : ℕ → ℕ)
    (k j r L : ℕ) (ω : PairedWalkTailTerminalSource A N k (j + r) L) :
    pairedWalkPast N (k + j) r
      (pairedWalkTerminalCast N (k + (j + r)) ((k + j) + r) L (Nat.add_assoc k j r).symm ω).1 =
        pairedWalkTailCheckpoint N k (j + r) L j (by omega) ω := by
  have transport (n n' : ℕ) (h : n = n') (q : ℕ) (hq : q < n + 1)
      (hq' : q < n' + 1) (ω : PairedWalkSource A N n) :
      pairedWalkCheckpoint N n' ⟨q, hq'⟩ (pairedWalkCast N n n' h ω) =
        pairedWalkCheckpoint N n ⟨q, hq⟩ ω := by
    subst n'
    rfl
  have h := transport (k + (j + r)) ((k + j) + r) (Nat.add_assoc k j r).symm
    (k + j) (by omega) (by omega) ω.1
  rw [pairedWalkCheckpoint_add] at h
  exact h

variable {A : Type*} [Fintype A] [MeasurableSpace A] [MeasurableSingletonClass A]

/-- The full remaining experiment, including its original terminal offset,
restarts EXACTLY from the intermediate full-history marginal. -/
theorem pairedWalkTailTerminalLaw_restart (z : ℕ → Point) (N : ℕ → ℕ) (b : A → ℕ)
    (k : ℕ) (ν : Measure (PairedWalkSource A N k)) [IsProbabilityMeasure ν]
    (j r L : ℕ) [NeZero L] :
    (pairedWalkTailTerminalLaw z N b k ν (j + r) L).map
      (pairedWalkTerminalCast N (k + (j + r)) ((k + j) + r) L (Nat.add_assoc k j r).symm) =
        pairedWalkTailTerminalLaw z N b (k + j) (pairedWalkTailLaw z N b k ν j) r L := by
  unfold pairedWalkTailTerminalLaw pairedWalkTerminalCast
  rw [← Measure.map_prod_map _ _ (measurable_of_finite _) measurable_id,
    Measure.map_id, pairedWalkTailLaw_restart]

/-- Map and conditioning commute on the ORIGINAL inverse-image event.
No positivity is required: zero fibers are equalities of measures. -/
theorem finite_map_cond_preimage {Ω Ω' : Type*} [Fintype Ω]
    [MeasurableSpace Ω] [MeasurableSingletonClass Ω]
    [MeasurableSpace Ω'] (μ : Measure Ω) (F : Ω → Ω') (E : Set Ω') (hE : MeasurableSet E) :
    (μ[|F ⁻¹' E]).map F = (μ.map F)[|E] := by
  unfold ProbabilityTheory.cond
  rw [Measure.map_smul, ← Measure.restrict_map (measurable_of_finite _) hE,
    Measure.map_apply (measurable_of_finite _) hE]
  exact (measurable_of_finite F).aemeasurable

/-- Conditional restart at ANY intermediate observation of the full history,
with the same original event and smoothing coordinate. Includes zero fibers. -/
theorem pairedWalkTailTerminalLaw_cond_restart (z : ℕ → Point) (N : ℕ → ℕ) (b : A → ℕ)
    (k : ℕ) (ν : Measure (PairedWalkSource A N k)) [IsProbabilityMeasure ν]
    (j r L : ℕ) [NeZero L] {B : Type*} [MeasurableSpace B] [MeasurableSingletonClass B]
    (V : PairedWalkSource A N (k + j) → B) (c : B) :
    ((pairedWalkTailTerminalLaw z N b k ν (j + r) L)[|
      (fun ω => V (pairedWalkTailCheckpoint N k (j + r) L j (by omega) ω)) ⁻¹' {c}]).map
        (pairedWalkTerminalCast N (k + (j + r)) ((k + j) + r) L (Nat.add_assoc k j r).symm) =
          pairedWalkTailTerminalLaw z N b (k + j) ((pairedWalkTailLaw z N b k ν j)[|V ⁻¹' {c}]) r L := by
  let F := pairedWalkTerminalCast (A := A) N (k + (j + r)) ((k + j) + r) L (Nat.add_assoc k j r).symm
  let W := fun ω : PairedWalkTailTerminalSource A N (k + j) r L => V (pairedWalkPast N (k + j) r ω.1)
  have he : (fun ω => V (pairedWalkTailCheckpoint N k (j + r) L j (by omega) ω)) ⁻¹' {c} =
      F ⁻¹' (W ⁻¹' {c}) := by
    ext ω
    simp only [Set.mem_preimage, Set.mem_singleton_iff, W, F, pairedWalkTerminalCast_checkpoint]
  rw [he, finite_map_cond_preimage _ F _ ((measurable_of_finite W) (MeasurableSet.singleton c)),
    pairedWalkTailTerminalLaw_restart]
  exact pairedWalkTailTerminalLaw_cond_checkpoint z N b (k + j) (pairedWalkTailLaw z N b k ν j) r L V c

/-- The actual terminal-time distribution on a conditioned intermediate fiber
is that of a fresh tail from its conditioned marginal. No terminal reconditioning. -/
theorem pairedWalkTailTerminalTime_cond_restart_identDistrib (z : ℕ → Point) (N : ℕ → ℕ)
    (b : A → ℕ) (k : ℕ) (ν : Measure (PairedWalkSource A N k)) [IsProbabilityMeasure ν]
    (j r L : ℕ) [NeZero L] {B : Type*} [MeasurableSpace B] [MeasurableSingletonClass B]
    (V : PairedWalkSource A N (k + j) → B) (c : B) :
    IdentDistrib (pairedWalkTailTerminalTime N b k (j + r) L)
      (pairedWalkTailTerminalTime N b (k + j) r L)
      ((pairedWalkTailTerminalLaw z N b k ν (j + r) L)[|
        (fun ω => V (pairedWalkTailCheckpoint N k (j + r) L j (by omega) ω)) ⁻¹' {c}])
      (pairedWalkTailTerminalLaw z N b (k + j) ((pairedWalkTailLaw z N b k ν j)[|V ⁻¹' {c}]) r L) := by
  refine ⟨(measurable_of_finite _).aemeasurable, (measurable_of_finite _).aemeasurable, ?_⟩
  have htime : pairedWalkTailTerminalTime (A := A) N b k (j + r) L =
      pairedWalkTailTerminalTime N b (k + j) r L ∘
        pairedWalkTerminalCast N (k + (j + r)) ((k + j) + r) L (Nat.add_assoc k j r).symm := by
    funext ω
    exact (pairedWalkTerminalCast_time N b k j r L ω).symm
  rw [htime, ← Measure.map_map (measurable_of_finite _) (measurable_of_finite _),
    pairedWalkTailTerminalLaw_cond_restart]

theorem pairedWalkTailTerminalLaw_intermediate_mass (z : ℕ → Point) (N : ℕ → ℕ)
    (b : A → ℕ) (k : ℕ) (ν : Measure (PairedWalkSource A N k))
    (j r L : ℕ) [NeZero L] {B : Type*} [MeasurableSpace B] [MeasurableSingletonClass B]
    (V : PairedWalkSource A N (k + j) → B) (c : B) :
    pairedWalkTailTerminalLaw z N b k ν (j + r) L
      ((fun ω => V (pairedWalkTailCheckpoint N k (j + r) L j (by omega) ω)) ⁻¹' {c}) =
        pairedWalkTailLaw z N b k ν j (V ⁻¹' {c}) := by
  change pairedWalkTailTerminalLaw z N b k ν (j + r) L
    ((pairedWalkTailCheckpoint N k (j + r) L j (by omega)) ⁻¹' (V ⁻¹' {c})) = _
  rw [← Measure.map_apply (measurable_of_finite _) ((measurable_of_finite V) (MeasurableSet.singleton c)),
    pairedWalkTailTerminalLaw_checkpoint_map]

end BinaryFormMoat.GeometryIntegration
#print axioms BinaryFormMoat.GeometryIntegration.pairedWalkTerminalCast
#print axioms BinaryFormMoat.GeometryIntegration.pairedWalkTerminalCast_time
#print axioms BinaryFormMoat.GeometryIntegration.pairedWalkTerminalCast_checkpoint
#print axioms BinaryFormMoat.GeometryIntegration.pairedWalkTailTerminalLaw_restart
#print axioms BinaryFormMoat.GeometryIntegration.finite_map_cond_preimage
#print axioms BinaryFormMoat.GeometryIntegration.pairedWalkTailTerminalLaw_cond_restart
#print axioms BinaryFormMoat.GeometryIntegration.pairedWalkTailTerminalTime_cond_restart_identDistrib
#print axioms BinaryFormMoat.GeometryIntegration.pairedWalkTailTerminalLaw_intermediate_mass
