import Integrations.SharedData435

namespace BinaryFormMoat.EntropyIntegration
open MeasureTheory ProbabilityTheory

/-- Recovering X from (Y,D) bounds entropy loss by the common displacement
entropy. X,Y,D may be fully dependent. -/
theorem entropy_loss_le_reconstruction {Ω T H : Type*}
    [Fintype Ω] [MeasurableSpace Ω] [MeasurableSingletonClass Ω]
    [Fintype T] [MeasurableSpace T] [MeasurableSingletonClass T]
    [Countable H] [MeasurableSpace H] [MeasurableSingletonClass H]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (X Y : Ω → T) (D : Ω → H)
    (recover : T → H → T) (hrec : ∀ ω, X ω = recover (Y ω) (D ω)) :
    entropy X μ - entropy D μ ≤ entropy Y μ := by
  have : FiniteRange D := ⟨Set.finite_range D⟩
  have he : X = (fun th : T × H => recover th.1 th.2) ∘ (fun ω => (Y ω, D ω)) :=
    funext hrec
  have hl : entropy X μ ≤ entropy (fun ω => (Y ω, D ω)) μ := by
    rw [he]
    exact entropy_comp_le μ (measurable_of_finite _) _
  have hu := entropy_pair_le_add (measurable_of_finite Y) (measurable_of_finite D) μ
  linarith

/-- A fixed auxiliary subset has the same reconstruction, so averaging pays
the common data entropy once, rather than once for each residue coordinate. -/
theorem labelSubsetJointEntropy_loss_le_reconstruction {Ω ι R H : Type*}
    [Fintype Ω] [MeasurableSpace Ω] [MeasurableSingletonClass Ω]
    [Fintype ι] [Fintype R] [Nonempty R]
    [Countable H] [MeasurableSpace H] [MeasurableSingletonClass H]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (G : ι × R → Type*)
    [∀ c, Fintype (G c)] [∀ c, MeasurableSpace (G c)]
    [∀ c, MeasurableSingletonClass (G c)]
    (X Y : ∀ c, Ω → G c) (D : Ω → H)
    (recover : ∀ c, G c → H → G c)
    (hrec : ∀ c ω, X c ω = recover c (Y c ω) (D ω))
    (s : ℕ) (hsk : s ≤ Fintype.card ι) :
    labelSubsetJointEntropy μ G X s - entropy D μ ≤ labelSubsetJointEntropy μ G Y s := by
  classical
  have h := subsetLabelAverage_mono s
    (fun A ρ => entropy (fun ω (i : A) => X (i.1, ρ i.1) ω) μ - entropy D μ)
    (fun A ρ => entropy (fun ω (i : A) => Y (i.1, ρ i.1) ω) μ) (by
      intro A _ ρ
      apply entropy_loss_le_reconstruction μ _ _ D
        (fun v h (i : A) => recover (i.1, ρ i.1) (v i) h)
      intro ω
      funext i
      exact hrec (i.1, ρ i.1) ω)
  rw [subsetLabelAverage_sub, subsetLabelAverage_const s hsk] at h
  exact h

/-- Additive residue maps reconstruct the old position by subtracting the
projected displacement from the new position. -/
theorem labelSubsetJointEntropy_loss_le_displacement {Ω ι R H : Type*}
    [Fintype Ω] [MeasurableSpace Ω] [MeasurableSingletonClass Ω]
    [Fintype ι] [Fintype R] [Nonempty R]
    [Countable H] [MeasurableSpace H] [MeasurableSingletonClass H]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (G : ι × R → Type*)
    [∀ c, Fintype (G c)] [∀ c, MeasurableSpace (G c)]
    [∀ c, MeasurableSingletonClass (G c)] [∀ c, AddCommGroup (G c)]
    (X Y : ∀ c, Ω → G c) (D : Ω → H) (φ : ∀ c, H → G c)
    (hadd : ∀ c ω, Y c ω = X c ω + φ c (D ω))
    (s : ℕ) (hsk : s ≤ Fintype.card ι) :
    labelSubsetJointEntropy μ G X s - entropy D μ ≤ labelSubsetJointEntropy μ G Y s := by
  apply labelSubsetJointEntropy_loss_le_reconstruction μ G X Y D
    (fun c v h => v - φ c h) _ s hsk
  intro c ω
  rw [hadd]
  simp

end BinaryFormMoat.EntropyIntegration

#print axioms BinaryFormMoat.EntropyIntegration.entropy_loss_le_reconstruction
#print axioms BinaryFormMoat.EntropyIntegration.labelSubsetJointEntropy_loss_le_reconstruction
#print axioms BinaryFormMoat.EntropyIntegration.labelSubsetJointEntropy_loss_le_displacement
