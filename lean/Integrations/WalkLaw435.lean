import Integrations.WalkDisplacement435
import Integrations.FiniteCheckpoint435
import Integrations.EntropyTransport435

namespace BinaryFormMoat.EntropyIntegration
open MeasureTheory ProbabilityTheory

section Walk
variable {Ω : Type*} [Fintype Ω] [MeasurableSpace Ω] [MeasurableSingletonClass Ω]
  (μ : Measure Ω) [IsProbabilityMeasure μ] (z : ℕ → Point) (R S : ℕ)
  (hstep : ∀ t, sqDist (z (t + 1)) (z t) ≤ (R : ℤ))
  {M : ℕ} (t : Ω → Fin M) (u : Ω → ℕ)
  (hforward : ∀ ω, (t ω).val ≤ u ω) (hshift : ∀ ω, u ω ≤ (t ω).val + S)

/-- Actual physical displacement, in a finite alphabet derived from the
graph step bound and the deterministic maximum future time shift. -/
def walkDisplacement (ω : Ω) : BoundedDisplacement ((R + 1) * S) :=
  ⟨z (u ω) - z (t ω).val,
    walk_displacement_mem z (R + 1) (sqDist_walk_coordinate_steps z R hstep)
      S (t ω).val (u ω) (hforward ω) (hshift ω)⟩

/-- The source law retains every dependency between the exact checkpoint
and terminal time. No uniform-time or independent-shift assumption is used. -/
noncomputable def walkCheckpointLaw :
    Measure (Fin M × BoundedDisplacement ((R + 1) * S)) :=
  finiteCheckpointLaw μ t (walkDisplacement z R S hstep t u hforward hshift)

instance walkCheckpointLaw_isProbabilityMeasure :
    IsProbabilityMeasure (walkCheckpointLaw μ z R S hstep t u hforward hshift) := by
  unfold walkCheckpointLaw
  infer_instance

omit [IsProbabilityMeasure μ] in
theorem walkCheckpointLaw_terminal_identDistrib {G : Type*}
    [AddCommGroup G] [MeasurableSpace G]
    (φ : Point →+ G) :
    IdentDistrib (fun ah : Fin M × BoundedDisplacement ((R + 1) * S) =>
      φ (z ah.1.val) + φ ah.2.val) (fun ω => φ (z (u ω)))
      (walkCheckpointLaw μ z R S hstep t u hforward hshift) μ := by
  have h := finiteCheckpointLaw_identDistrib μ t
    (walkDisplacement z R S hstep t u hforward hshift)
    (fun ah => φ (z ah.1.val) + φ ah.2.val)
  have he : (fun ω => φ (z (t ω).val) +
      φ (walkDisplacement z R S hstep t u hforward hshift ω).val) =
      (fun ω => φ (z (u ω))) := by
    funext ω
    change φ (z (t ω).val) + φ (z (u ω) - z (t ω).val) = _
    rw [map_sub]
    abel
  rw [he] at h
  exact h

omit [IsProbabilityMeasure μ] in
theorem walkCheckpointLaw_cond_terminal_identDistrib {G : Type*}
    [AddCommGroup G] [MeasurableSpace G] (φ : Point →+ G) (a : Fin M) :
    IdentDistrib (fun ah : Fin M × BoundedDisplacement ((R + 1) * S) =>
      φ (z ah.1.val) + φ ah.2.val) (fun ω => φ (z (u ω)))
      ((walkCheckpointLaw μ z R S hstep t u hforward hshift)[|Prod.fst ⁻¹' {a}])
      (μ[|t ⁻¹' {a}]) := by
  have h := finiteCheckpointLaw_cond_identDistrib μ t
    (walkDisplacement z R S hstep t u hforward hshift)
    (fun ah => φ (z ah.1.val) + φ ah.2.val) a
  have he : (fun ω => φ (z (t ω).val) +
      φ (walkDisplacement z R S hstep t u hforward hshift ω).val) =
      (fun ω => φ (z (u ω))) := by
    funext ω
    change φ (z (t ω).val) + φ (z (u ω) - z (t ω).val) = _
    rw [map_sub]
    abel
  rw [he] at h
  exact h

omit [IsProbabilityMeasure μ] in
theorem walkCheckpointLaw_labelSubsetJointEntropy {ι Q : Type*}
    [Fintype ι] [Fintype Q] (G : ι × Q → Type*)
    [∀ c, MeasurableSpace (G c)] (φ : ∀ c, Point → G c) (s : ℕ) :
    labelSubsetJointEntropy (walkCheckpointLaw μ z R S hstep t u hforward hshift) G
      (fun c ah => φ c (z ah.1.val)) s =
        labelSubsetJointEntropy μ G (fun c ω => φ c (z (t ω).val)) s :=
  finiteCheckpointLaw_labelSubsetJointEntropy μ t
    (walkDisplacement z R S hstep t u hforward hshift) G
    (fun c a => φ c (z a.val)) s

include hstep hforward hshift

omit [IsProbabilityMeasure μ] in
theorem walk_displacement_entropy_le :
    entropy (fun ω => z (u ω) - z (t ω).val) μ ≤
      2 * Real.log (2 * ((R + 1) * S) + 1 : ℕ) := by
  have h := entropy_le_log_card_of_mem (A := displacementBox ((R + 1) * S))
    (measurable_of_finite (fun ω => z (u ω) - z (t ω).val))
    (ae_of_all μ (fun ω =>
      (walkDisplacement z R S hstep t u hforward hshift ω).property))
  simpa only [displacementBox_card, Nat.cast_pow, Real.log_pow, Nat.cast_ofNat] using h

omit [IsProbabilityMeasure μ] [Fintype Ω] [MeasurableSingletonClass Ω] in
theorem walk_resampled_data_entropy_le {J : Type*} [Fintype J] :
    entropy (Prod.snd : Fin M × (J → BoundedDisplacement ((R + 1) * S)) →
      J → BoundedDisplacement ((R + 1) * S))
        (originalResamplingLaw (walkCheckpointLaw μ z R S hstep t u hforward hshift)
          (zeroDisplacement ((R + 1) * S))) ≤
      (Fintype.card J : ℝ) * (2 * Real.log (2 * ((R + 1) * S) + 1 : ℕ)) :=
  boundedDisplacement_data_entropy_le _ _

/-- High checkpoint residue entropy persists at the terminal time with one
logarithmic displacement cost, for every auxiliary subset and label law. -/
theorem walk_labelSubsetJointEntropy_transport {ι Q : Type*}
    [Fintype ι] [Fintype Q] [Nonempty Q] (G : ι × Q → Type*)
    [∀ c, Fintype (G c)] [∀ c, MeasurableSpace (G c)]
    [∀ c, MeasurableSingletonClass (G c)] [∀ c, AddCommGroup (G c)]
    (φ : ∀ c, Point →+ G c) (s : ℕ) (hsk : s ≤ Fintype.card ι) :
    labelSubsetJointEntropy μ G (fun c ω => φ c (z (t ω).val)) s -
      2 * Real.log (2 * ((R + 1) * S) + 1 : ℕ) ≤
        labelSubsetJointEntropy μ G (fun c ω => φ c (z (u ω))) s := by
  have hl := labelSubsetJointEntropy_loss_le_displacement μ G
    (fun c ω => φ c (z (t ω).val)) (fun c ω => φ c (z (u ω)))
    (fun ω => z (u ω) - z (t ω).val) (fun c => φ c) (by
      intro c ω
      rw [map_sub]
      abel) s hsk
  have hu := walk_displacement_entropy_le μ z R S hstep t u hforward hshift
  linarith

omit [IsProbabilityMeasure μ] in
theorem walk_displacement_entropy_source_bound (L : ℝ)
    (hS : Real.log (S + 1 : ℕ) ≤ L) :
    entropy (fun ω => z (u ω) - z (t ω).val) μ ≤
      2 * L + 2 * Real.log (2 * (R + 1) + 1 : ℕ) := by
  have h := (walk_displacement_entropy_le μ z R S hstep t u hforward hshift).trans
    (displacement_log_bound (R + 1) S)
  linarith

end Walk
end BinaryFormMoat.EntropyIntegration

#print axioms BinaryFormMoat.EntropyIntegration.walkCheckpointLaw_isProbabilityMeasure
#print axioms BinaryFormMoat.EntropyIntegration.walkCheckpointLaw_terminal_identDistrib
#print axioms BinaryFormMoat.EntropyIntegration.walkCheckpointLaw_cond_terminal_identDistrib
#print axioms BinaryFormMoat.EntropyIntegration.walkCheckpointLaw_labelSubsetJointEntropy
#print axioms BinaryFormMoat.EntropyIntegration.walk_displacement_entropy_le
#print axioms BinaryFormMoat.EntropyIntegration.walk_resampled_data_entropy_le
#print axioms BinaryFormMoat.EntropyIntegration.walk_labelSubsetJointEntropy_transport
#print axioms BinaryFormMoat.EntropyIntegration.walk_displacement_entropy_source_bound
