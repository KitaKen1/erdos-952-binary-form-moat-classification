import Integrations.GeometricResidueAlphabet435

noncomputable section
open scoped Classical
namespace BinaryFormMoat.GeometryIntegration
open EntropyIntegration MeasureTheory ProbabilityTheory

/-- Auxiliary subsets and labels are fixed inside each conditional entropy.
The averaging does not add their entropy to the sampled walk law. -/
def labelledPointCondEntropyMean {Ω ι Q U : Type*}
    [MeasurableSpace Ω] [Fintype ι] [DecidableEq ι] [Fintype Q] [MeasurableSpace U]
    (K : ι → Type*) [∀ i, AddCommGroup (K i)] [∀ i, Fintype (K i)]
    [∀ i, MeasurableSpace (K i)] [∀ i, MeasurableSingletonClass (K i)]
    (F : ∀ i, Q → Point →+ K i) (μ : Measure Ω) (s : ℕ) (X : Ω → Point) (O : Ω → U) : ℝ :=
  subsetLabelAverage s (fun A ρ =>
    condEntropy (subsetObservation K (fun i ω => F i (ρ i) (X ω)) A) O μ)

/-- Fixed prior residue data costs H(O) ONCE, after averaging the target
prime subset and root labels. Coordinate independence is not required. -/
theorem labelledPointCondEntropyMean_ge {Ω ι Q U : Type*}
    [Fintype Ω] [MeasurableSpace Ω] [MeasurableSingletonClass Ω]
    [Fintype ι] [DecidableEq ι] [Fintype Q] [Nonempty Q]
    [Fintype U] [MeasurableSpace U] [MeasurableSingletonClass U]
    (K : ι → Type*) [∀ i, AddCommGroup (K i)] [∀ i, Fintype (K i)]
    [∀ i, MeasurableSpace (K i)] [∀ i, MeasurableSingletonClass (K i)]
    (F : ∀ i, Q → Point →+ K i) (μ : Measure Ω) [IsProbabilityMeasure μ]
    (s : ℕ) (hs : s ≤ Fintype.card ι) (X : Ω → Point) (O : Ω → U) :
    labelledPointEntropyMean K F μ s X - entropy O μ ≤
      labelledPointCondEntropyMean K F μ s X O := by
  have h := subsetLabelAverage_mono s
    (fun A ρ => entropy (subsetObservation K (fun i ω => F i (ρ i) (X ω)) A) μ - entropy O μ)
    (fun A ρ => condEntropy (subsetObservation K (fun i ω => F i (ρ i) (X ω)) A) O μ)
    (fun _ _ _ => condEntropy_ge_entropy_sub_observation_entropy μ _ O
      (measurable_of_finite _) (measurable_of_finite _))
  rw [subsetLabelAverage_sub, subsetLabelAverage_const s hs] at h
  exact h

/-- The joint band's top certificate supplies ACTUAL common-terminal
entropy for its SAME batch. High entropy is a conclusion, not a premise. -/
theorem PaperJointBatch.terminal_entropy
    {A Q : Type*} [Fintype A] [MeasurableSpace A] [MeasurableSingletonClass A]
    [Fintype Q] [Nonempty Q]
    (f : Polynomial ℤ) (hf : Irreducible f) (hd : 2 ≤ f.natDegree)
    (R M : ℕ) (m : Fin (M + 1)) (hm : (M + 1) / 2 ≤ m.val)
    (g0 c a0 : ℝ) (l T : ℕ) (hl : 1 ≤ l) (hT : 2 ≤ T) (bad P : Finset ℕ)
    [∀ p : P, NeZero p.val] (batch : PaperJointBatch f R M m g0 c a0 l T bad P)
    (e : ∀ p : P, Q ≃ primeRootSet f p.val)
    (z : ℕ → Point) (a : A → ℕ) (k : ℕ)
    (ν : Measure (PairedWalkSource A (paperScheduleWindow f.natDegree M g0) k))
    [IsProbabilityMeasure ν]
    (hbefore : k ≤ paperOpPosition (paperBlockOp (d := f.natDegree) g0 m 0 (a0 * T) 0
      (by have := batch.top.fit; omega)))
    (hstep : ∀ t, sqDist (z (t + 1)) (z t) ≤ (R : ℤ)) (hinj : Function.Injective z) :
    let q := paperInputRank (paperBlockScale f.natDegree M m.val g0 0 (a0 * T) l)
      (primeBatchLogMean P)
    (1 - 90 * g0 - (1 / 2 : ℝ) ^ l) * ((q : ℝ) * primeBatchLogMean P) ≤
      labelledPointEntropyMean (fun p : P => ZMod p.val)
        (labelledPrimeResidue P (primeRootSet f) e)
        (paperFullTailLaw z f.natDegree M g0 a k ν) q
        (fun ω => z (paperFullTailTerminalTime f.natDegree M g0 a k ω)) := by
  dsimp only
  have hL := primeBatchLogMean_dyadic_bounds P T hT batch.nonempty
    (fun p hp => (batch.primes p hp).2.1) (fun p hp => (batch.primes p hp).2.2.1)
  have hq := PaperJointBatch.record_inventory f R M m g0 c a0 l T bad P batch hl hT
  have high := paperBlockCertificate_tail_terminal_entropy f hf hd M R m hm g0 0 (a0 * T) l T hl P
    (fun p hp => (batch.primes p hp).1) (primeRootSet f)
    (fun p hp => (batch.primes p hp).2.2.2)
    (fun p hp ρ hρ => (mem_primeRootSet f p (batch.primes p hp).1 ρ).mp hρ) e
    hT batch.nonempty (fun p hp => (batch.primes p hp).2.1)
    (fun p hp => (batch.primes p hp).2.2.1) batch.top z a k
    (paperScheduleList f.natDegree M g0).length ν hbefore
    (paperOpPosition_lt _ (paperBlockOp_mem g0 m hm 0 (a0 * T) l batch.top.fit)).le
    le_rfl hstep hinj
  simp only [paperBandG, ↓reduceIte] at high
  exact (le_div_iff₀ (mul_pos (by exact_mod_cast hq.1) hL.1)).mp high

/-- Every top recording operation precedes every middle start in its
original window. This order follows from the actual schedule, not scale lore. -/
theorem PaperJointBatch.top_record_before_middle (f : Polynomial ℤ) (R M : ℕ)
    (m : Fin (M + 1)) (hm : (M + 1) / 2 ≤ m.val) (g0 c a0 : ℝ)
    (l T i : ℕ) (bad P : Finset ℕ) (batch : PaperJointBatch f R M m g0 c a0 l T bad P) :
    paperOpPosition (paperBlockOp (d := f.natDegree) g0 m 0 (a0 * T) l batch.top.fit) ≤
      paperMiddleStartPosition f M R m g0 T i P (batch.middle i) := by
  apply (paperOpPosition_le_iff _ _ (paperBlockOp_mem g0 m hm 0 (a0 * T) l batch.top.fit)
    (paperMiddleStartOp_mem f M R m hm g0 T i P (batch.middle i))).mpr
  unfold paperOpLater
  right; left
  exact ⟨rfl, by change (0 : Fin 3) < 1; decide⟩

/-- Persistent top entropy at ANY actual middle start, read on the SAME
full terminal source. This is the checkpoint prior needed by the information
argument; terminal entropy alone would not supply that prior. -/
theorem PaperJointBatch.middle_start_entropy
    {A Q : Type*} [Fintype A] [MeasurableSpace A] [MeasurableSingletonClass A]
    [Fintype Q] [Nonempty Q]
    (f : Polynomial ℤ) (hf : Irreducible f) (hd : 2 ≤ f.natDegree)
    (R M : ℕ) (m : Fin (M + 1)) (hm : (M + 1) / 2 ≤ m.val)
    (g0 c a0 : ℝ) (l T i : ℕ) (hl : 1 ≤ l) (hT : 2 ≤ T) (bad P : Finset ℕ)
    [∀ p : P, NeZero p.val] (batch : PaperJointBatch f R M m g0 c a0 l T bad P)
    (e : ∀ p : P, Q ≃ primeRootSet f p.val)
    (z : ℕ → Point) (a : A → ℕ) (k : ℕ)
    (ν : Measure (PairedWalkSource A (paperScheduleWindow f.natDegree M g0) k))
    [IsProbabilityMeasure ν]
    (hbefore : k ≤ paperOpPosition (paperBlockOp (d := f.natDegree) g0 m 0 (a0 * T) 0
      (by have := batch.top.fit; omega)))
    (hstep : ∀ t, sqDist (z (t + 1)) (z t) ≤ (R : ℤ)) (hinj : Function.Injective z) :
    let q := paperInputRank (paperBlockScale f.natDegree M m.val g0 0 (a0 * T) l)
      (primeBatchLogMean P)
    let r := paperMiddleStartPosition f M R m g0 T i P (batch.middle i)
    let hr : r ≤ (paperScheduleList f.natDegree M g0).length :=
      (paperOpPosition_lt _ (paperMiddleStartOp_mem f M R m hm g0 T i P (batch.middle i))).le
    (1 - 90 * g0 - (1 / 2 : ℝ) ^ l) * ((q : ℝ) * primeBatchLogMean P) ≤
      labelledPointEntropyMean (fun p : P => ZMod p.val)
        (labelledPrimeResidue P (primeRootSet f) e)
        (paperFullTailLaw z f.natDegree M g0 a k ν) q
        (fun ω => z (paperFullTailCheckpointTime f.natDegree M g0 a k r hr ω)) := by
  dsimp only
  simp only [paperMiddleStartPosition]
  rw [labelledPointEntropyMean_eq_joint,
    paperFullTailLaw_checkpoint_jointEntropy z f.natDegree M g0 a k _ _ ν
      (fun c : P × Q => ZMod c.1.val)
      (fun c x => labelledPrimeResidue P (primeRootSet f) e c.1 c.2 x)]
  have hL := primeBatchLogMean_dyadic_bounds P T hT batch.nonempty
    (fun p hp => (batch.primes p hp).2.1) (fun p hp => (batch.primes p hp).2.2.1)
  have hq := PaperJointBatch.record_inventory f R M m g0 c a0 l T bad P batch hl hT
  have high := paperBlockCertificate_tail_later_entropy f hf hd M R m hm g0 0 (a0 * T) l T hl P
    (fun p hp => (batch.primes p hp).1) (primeRootSet f)
    (fun p hp => (batch.primes p hp).2.2.2)
    (fun p hp ρ hρ => (mem_primeRootSet f p (batch.primes p hp).1 ρ).mp hρ) e
    hT batch.nonempty (fun p hp => (batch.primes p hp).2.1)
    (fun p hp => (batch.primes p hp).2.2.1) batch.top z a k
    (paperMiddleStartPosition f M R m g0 T i P (batch.middle i)) ν hbefore
    (PaperJointBatch.top_record_before_middle f R M m hm g0 c a0 l T i bad P batch)
    (paperOpPosition_lt _ (paperMiddleStartOp_mem f M R m hm g0 T i P (batch.middle i))).le hstep hinj
  simp only [paperBandG, ↓reduceIte] at high
  exact (le_div_iff₀ (mul_pos (by exact_mod_cast hq.1) hL.1)).mp high

/-- Under ANY finite law, the smaller-family alphabet bound lowers the
auxiliary-averaged conditional entropy by at most epsilon*q*TRUE_mean.
The persistent entropy premise is supplied by the actual top certificate. -/
theorem labelledPointCondEntropyMean_accuracy {Ω ι Q U : Type*}
    [Fintype Ω] [MeasurableSpace Ω] [MeasurableSingletonClass Ω]
    [Fintype ι] [DecidableEq ι] [Fintype Q] [Nonempty Q]
    [Fintype U] [MeasurableSpace U] [MeasurableSingletonClass U]
    (K : ι → Type*) [∀ i, AddCommGroup (K i)] [∀ i, Fintype (K i)]
    [∀ i, MeasurableSpace (K i)] [∀ i, MeasurableSingletonClass (K i)]
    (F : ∀ i, Q → Point →+ K i) (μ : Measure Ω) [IsProbabilityMeasure μ]
    (s : ℕ) (hs : s ≤ Fintype.card ι) (X : Ω → Point) (O : Ω → U)
    (ε H : ℝ) (hX : (1 - ε) * H ≤ labelledPointEntropyMean K F μ s X)
    (hO : entropy O μ ≤ ε * H) :
    (1 - 2 * ε) * H ≤ labelledPointCondEntropyMean K F μ s X O := by
  have h := labelledPointCondEntropyMean_ge K F μ s hs X O
  linarith

end BinaryFormMoat.GeometryIntegration
#print axioms BinaryFormMoat.GeometryIntegration.labelledPointCondEntropyMean
#print axioms BinaryFormMoat.GeometryIntegration.labelledPointCondEntropyMean_ge
#print axioms BinaryFormMoat.GeometryIntegration.PaperJointBatch.terminal_entropy
#print axioms BinaryFormMoat.GeometryIntegration.PaperJointBatch.top_record_before_middle
#print axioms BinaryFormMoat.GeometryIntegration.PaperJointBatch.middle_start_entropy
#print axioms BinaryFormMoat.GeometryIntegration.labelledPointCondEntropyMean_accuracy
