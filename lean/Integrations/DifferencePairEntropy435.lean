import Integrations.DifferencePairLaw435
import Integrations.MixedCoordinateFloor435

noncomputable section
namespace BinaryFormMoat.GeometryIntegration
open EntropyIntegration MeasureTheory ProbabilityTheory

section Forward
variable {A : Type*} [Fintype A] [MeasurableSpace A] [MeasurableSingletonClass A]
  (z : ℕ → Point) (N : ℕ) (μ : Measure A) [IsProbabilityMeasure μ] (b : A → ℕ)

omit [IsProbabilityMeasure μ] in
/-- Every original-base observation retains its exact entropy. -/
theorem differencePairForwardLaw_base_observation_entropy {Q : Type*} [MeasurableSpace Q]
    (f : A → Q) :
    entropy (fun ω : DifferencePairSource A N => f ω.1) (differencePairForwardLaw z N μ b) =
      entropy f μ := by
  rw [entropy_def, entropy_def,
    show (fun ω : DifferencePairSource A N => f ω.1) = f ∘ Prod.fst from rfl,
    ← Measure.map_map (measurable_of_finite f) measurable_fst,
    differencePairForwardLaw_base_map]

/-- Arbitrary endpoint-pair observations transport on the exact positive base fiber. -/
theorem differencePairForwardLaw_cond_observation_entropy {Q : Type*} [MeasurableSpace Q]
    (f : Point × Point → Q) (a : A) (ha : μ {a} ≠ 0) :
    entropy (fun ω => f (z (differencePairFirstTime N b ω), z (differencePairSecondTime N b ω)))
      ((differencePairForwardLaw z N μ b)[|Prod.fst ⁻¹' {a}]) =
    entropy (fun h : WalkDifferences (fun k => z (b a + k)) N =>
      f (z (b a + (walkDifferenceTimes (fun k => z (b a + k)) N h).1.val),
        z (b a + (walkDifferenceTimes (fun k => z (b a + k)) N h).2.val)))
      (uniformOn (Set.univ : Set (WalkDifferences (fun k => z (b a + k)) N))) := by
  have hm := congrArg (fun m : Measure (Point × Point) => m.map f)
    (differencePairForwardLaw_cond_endpoint_map z N μ b a ha)
  rw [Measure.map_map (measurable_of_countable f) (measurable_of_finite _),
    Measure.map_map (measurable_of_countable f) (measurable_of_finite _)] at hm
  exact congrArg (fun m : Measure Q => measureEntropy m) hm

theorem differencePairForwardLaw_cond_observation_condEntropy {Q O : Type*}
    [Countable Q] [MeasurableSpace Q] [MeasurableSingletonClass Q]
    [Countable O] [MeasurableSpace O] [MeasurableSingletonClass O]
    (f : Point × Point → Q) (g : Point × Point → O) (a : A) (ha : μ {a} ≠ 0) :
    condEntropy (fun ω => f (z (differencePairFirstTime N b ω), z (differencePairSecondTime N b ω)))
      (fun ω => g (z (differencePairFirstTime N b ω), z (differencePairSecondTime N b ω)))
      ((differencePairForwardLaw z N μ b)[|Prod.fst ⁻¹' {a}]) =
    condEntropy (fun h : WalkDifferences (fun k => z (b a + k)) N =>
      f (z (b a + (walkDifferenceTimes (fun k => z (b a + k)) N h).1.val),
        z (b a + (walkDifferenceTimes (fun k => z (b a + k)) N h).2.val)))
      (fun h : WalkDifferences (fun k => z (b a + k)) N =>
      g (z (b a + (walkDifferenceTimes (fun k => z (b a + k)) N h).1.val),
        z (b a + (walkDifferenceTimes (fun k => z (b a + k)) N h).2.val)))
      (uniformOn (Set.univ : Set (WalkDifferences (fun k => z (b a + k)) N))) := by
  rw [chain_rule'' _ (measurable_of_finite _) (measurable_of_finite _),
    chain_rule'' _ (measurable_of_finite _) (measurable_of_finite _)]
  rw [differencePairForwardLaw_cond_observation_entropy z N μ b (fun p => (f p, g p)) a ha,
    differencePairForwardLaw_cond_observation_entropy z N μ b g a ha]

section Coordinates
variable {ι R : Type*} [Fintype ι] [DecidableEq ι] [Fintype R]
  (K : ι → Type*) [∀ i, AddCommGroup (K i)] [∀ i, Fintype (K i)]
  [∀ i, MeasurableSpace (K i)] [∀ i, MeasurableSingletonClass (K i)]
  (F : ∀ i, R → Point →+ K i)

omit [IsProbabilityMeasure μ] [DecidableEq ι] [∀ i, Fintype (K i)]
  [∀ i, MeasurableSingletonClass (K i)] in
/-- Starting q-tuple prior is exactly that of the ORIGINAL base law. -/
theorem differencePairForwardLaw_labelled_base_entropy (q : ℕ) :
    labelledPointEntropyMean K F (differencePairForwardLaw z N μ b) q (fun ω => z (b ω.1)) =
      labelledPointEntropyMean K F μ q (fun a => z (b a)) := by
  unfold labelledPointEntropyMean subsetLabelAverage
  congr 1
  apply Finset.sum_congr rfl
  intro S _
  congr 1
  apply Finset.sum_congr rfl
  intro ρ _
  exact differencePairForwardLaw_base_observation_entropy z N μ b
    (fun a (i : S) => F i.val (ρ i.val) (z (b a)))

/-- The entire conditional G_s floor is identified, including both prefix observations. -/
theorem differencePairForwardLaw_fiber_floor_eq (s : ℕ) (a : A) (ha : μ {a} ≠ 0) :
    labelledPointDifferenceFloor K F ((differencePairForwardLaw z N μ b)[|Prod.fst ⁻¹' {a}]) s
      (fun ω => z (differencePairFirstTime N b ω)) (fun ω => z (differencePairSecondTime N b ω)) =
    labelledPointDifferenceFloor K F
      (uniformOn (Set.univ : Set (WalkDifferences (fun k => z (b a + k)) N))) s
      (fun h => z (b a + (walkDifferenceTimes (fun k => z (b a + k)) N h).1.val))
      (fun h => z (b a + (walkDifferenceTimes (fun k => z (b a + k)) N h).2.val)) := by
  unfold labelledPointDifferenceFloor subsetLabelAverage
  congr 1
  apply Finset.sum_congr rfl
  intro S _
  congr 1
  apply Finset.sum_congr rfl
  intro ρ _
  apply Finset.sum_congr rfl
  intro i _
  exact differencePairForwardLaw_cond_observation_condEntropy z N μ b
    (fun p => F i (ρ i) (p.1 - p.2))
    (fun p => ((fun (j : S) => F j.val (ρ j.val) p.1),
      (fun (j : S) => F j.val (ρ j.val) p.2))) a ha

variable [Nonempty R]

/-- Actual base-fiber geometry; the separation-failure bound remains explicit. -/
theorem differencePairForwardLaw_fiber_geometric_floor (s r D T : ℕ) (a : A) (ha : μ {a} ≠ 0)
    (hstep : ∀ t, |(z (t + 1)).1 - (z t).1| ≤ D ∧ |(z (t + 1)).2 - (z t).2| ≤ D)
    (hinj : ∀ i ≤ N, ∀ j ≤ N, z (b a + i) = z (b a + j) → i = j)
    (hr : 1 ≤ r) (hsr : s + r ≤ Fintype.card ι)
    (hcard : ∀ i, Fintype.card (K i) ≤ 2 * T) (ε : ℝ) (hε : ε ≤ 1)
    (herr : badLabelledSubsetFraction K (fun i x => F i x)
      (pointDifferences (walkVertexSet (fun k => z (b a + k)) N)) r ≤ ε) :
    ((1 - ε) * (Real.log (prefixArea (fun k => z (b a + k)) N : ℝ) -
      2 * Real.log (4 * D + 1 : ℕ)) - 2 * (s : ℝ) * Real.log (2 * T : ℕ)) / r ≤
    labelledPointDifferenceFloor K F ((differencePairForwardLaw z N μ b)[|Prod.fst ⁻¹' {a}]) s
      (fun ω => z (differencePairFirstTime N b ω)) (fun ω => z (differencePairSecondTime N b ω)) /
        (Fintype.card ι - s : ℕ) := by
  rw [differencePairForwardLaw_fiber_floor_eq z N μ b K F s a ha]
  apply uniformWalk_labelledPointDifferenceFloor_ge K F (fun k => z (b a + k)) D N s r T
    _ hinj hr hsr hcard ε hε herr
  intro t _
  simpa only [Nat.add_assoc] using hstep (b a + t)

/-- Every positive base fiber supplies its actual geometric floor. Exact weights
and conditioning removal yield one G_s floor on the original paired law. -/
theorem differencePairForwardLaw_geometric_floor (s D T : ℕ) (hs : s < Fintype.card ι)
    (r : A → ℕ) (ε : A → ℝ) (L : ℝ)
    (hstep : ∀ t, |(z (t + 1)).1 - (z t).1| ≤ D ∧ |(z (t + 1)).2 - (z t).2| ≤ D)
    (hinj : ∀ a, μ {a} ≠ 0 → ∀ i ≤ N, ∀ j ≤ N, z (b a + i) = z (b a + j) → i = j)
    (hr : ∀ a, μ {a} ≠ 0 → 1 ≤ r a)
    (hsr : ∀ a, μ {a} ≠ 0 → s + r a ≤ Fintype.card ι)
    (hcard : ∀ i, Fintype.card (K i) ≤ 2 * T)
    (hε : ∀ a, μ {a} ≠ 0 → ε a ≤ 1)
    (herr : ∀ a, μ {a} ≠ 0 → badLabelledSubsetFraction K (fun i x => F i x)
      (pointDifferences (walkVertexSet (fun k => z (b a + k)) N)) (r a) ≤ ε a)
    (hnumeric : ∀ a, μ {a} ≠ 0 → L ≤
      ((1 - ε a) * (Real.log (prefixArea (fun k => z (b a + k)) N : ℝ) -
        2 * Real.log (4 * D + 1 : ℕ)) - 2 * (s : ℝ) * Real.log (2 * T : ℕ)) / r a) :
    (Fintype.card ι - s : ℕ) * L ≤
      labelledPointDifferenceFloor K F (differencePairForwardLaw z N μ b) s
        (fun ω => z (differencePairFirstTime N b ω)) (fun ω => z (differencePairSecondTime N b ω)) := by
  have hc : (0 : ℝ) < (Fintype.card ι - s : ℕ) := by exact_mod_cast Nat.sub_pos_of_lt hs
  have hg := labelledPointDifferenceFloor_ge_uniform_fiber_floor K F (differencePairForwardLaw z N μ b)
    Prod.fst s (fun ω => z (differencePairFirstTime N b ω))
    (fun ω => z (differencePairSecondTime N b ω)) hs L (by
      intro a haReal
      rw [differencePairForwardLaw_real_base_fiber] at haReal
      have ha : μ {a} ≠ 0 := by
        intro hz
        exact haReal (by simp [measureReal_def, hz])
      have hf := differencePairForwardLaw_fiber_geometric_floor z N μ b K F s (r a) D T a ha
        hstep (hinj a ha) (hr a ha) (hsr a ha) hcard (ε a) (hε a ha) (herr a ha)
      have h := (le_div_iff₀ hc).mp ((hnumeric a ha).trans hf)
      simpa only [mul_comm] using h)
  have h := (le_div_iff₀ hc).mp hg
  simpa only [mul_comm] using h

end Coordinates
end Forward
end BinaryFormMoat.GeometryIntegration

#print axioms BinaryFormMoat.GeometryIntegration.differencePairForwardLaw_base_observation_entropy
#print axioms BinaryFormMoat.GeometryIntegration.differencePairForwardLaw_cond_observation_entropy
#print axioms BinaryFormMoat.GeometryIntegration.differencePairForwardLaw_cond_observation_condEntropy
#print axioms BinaryFormMoat.GeometryIntegration.differencePairForwardLaw_labelled_base_entropy
#print axioms BinaryFormMoat.GeometryIntegration.differencePairForwardLaw_fiber_floor_eq
#print axioms BinaryFormMoat.GeometryIntegration.differencePairForwardLaw_fiber_geometric_floor
#print axioms BinaryFormMoat.GeometryIntegration.differencePairForwardLaw_geometric_floor
