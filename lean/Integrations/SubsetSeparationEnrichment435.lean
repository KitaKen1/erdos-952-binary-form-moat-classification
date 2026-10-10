import Integrations.SubsetRootSeparation435
import Integrations.PairedConditionalEnrichment435

noncomputable section
open scoped Classical
namespace BinaryFormMoat.GeometryIntegration
open EntropyIntegration HarperIntegration MeasureTheory ProbabilityTheory

/-- Specialize the geometric floor to actual prime-root coordinates, deriving
its bad fraction from batch budgets instead of assuming a separation bound.
The redundant NeZero instances follow from hP. -/
theorem rounded_prime_subset_uniformWalk_floor {R : Type*} [Fintype R] [Nonempty R]
    (f : Polynomial ℤ) (hf : Irreducible f) (hd : 2 ≤ f.natDegree)
    (z : ℕ → Point) (D N b : ℕ)
    (hstep : ∀ t < N, |(z (t + 1)).1 - (z t).1| ≤ D ∧ |(z (t + 1)).2 - (z t).2| ≤ D)
    (hinj : ∀ i ≤ N, ∀ j ≤ N, z i = z j → i = j)
    (P : Finset ℕ) [∀ p : P, NeZero p.val] (hP : ∀ p ∈ P, p.Prime)
    (S : (p : ℕ) → Finset (ZMod p)) (hcard : ∀ p ∈ P, (S p).card = f.natDegree)
    (hroot : ∀ p ∈ P, ∀ ρ ∈ S p, f.eval₂ (Int.castRingHom (ZMod p)) ρ = 0)
    (e : ∀ p : P, R ≃ S p.val) (T r : ℕ) (hT : 2 ≤ T) (hr : 0 < r)
    (η g : ℝ) (hη : 0 < η) (hη1 : η ≤ 1) (hg : 0 < g)
    (hbr : b + roundedHarperCount (harperQuotaWidth η) r ≤ P.card)
    (hlo : ∀ p ∈ P, T ≤ p) (hhi : ∀ p ∈ P, p ≤ 2 * T)
    (hbudget : RoundedSubsetSeparationBudget f z D N P T r η g)
    (hε : roundedSubsetFailureBound P f.natDegree r η g ≤ 1) :
    ((1 - roundedSubsetFailureBound P f.natDegree r η g) *
        (Real.log (prefixArea z N : ℝ) - 2 * Real.log (4 * D + 1 : ℕ)) -
      2 * (b : ℝ) * Real.log (2 * T : ℕ)) / roundedHarperCount (harperQuotaWidth η) r ≤
    labelledPointDifferenceFloor (fun p : P => ZMod p.val) (labelledPrimeResidue P S e)
      (uniformOn (Set.univ : Set (WalkDifferences z N))) b
      (fun h => z (walkDifferenceTimes z N h).1.val)
      (fun h => z (walkDifferenceTimes z N h).2.val) / (Fintype.card P - b : ℕ) := by
  have hq : 0 < harperQuotaWidth η := by
    have h := (harperQuotaWidth_schedule η hη).1
    omega
  have hcount := (roundedHarperCount_bounds (harperQuotaWidth η) r hq).1
  apply uniformWalk_labelledPointDifferenceFloor_ge (fun p : P => ZMod p.val)
    (labelledPrimeResidue P S e) z D N b _ T hstep hinj (by omega)
    (by simpa using hbr) (fun p => by simpa using hhi p.val p.property) _ hε
  exact rounded_prime_subset_bad_fraction_le f hf hd z D N hstep P hP S hcard hroot
    e T r hT hr η g hη hη1 hg (by omega) hlo hhi hbudget

section Paired
variable {A R : Type*} [Fintype A] [MeasurableSpace A] [MeasurableSingletonClass A]
  [Fintype R] [Nonempty R]
  (f : Polynomial ℤ) (hf : Irreducible f) (hd : 2 ≤ f.natDegree)
  (z : ℕ → Point) (N : ℕ) (μ : Measure A) [IsProbabilityMeasure μ] (b : A → ℕ)
  (P : Finset ℕ) [∀ p : P, NeZero p.val] (hP : ∀ p ∈ P, p.Prime)
  (S : (p : ℕ) → Finset (ZMod p)) (hcard : ∀ p ∈ P, (S p).card = f.natDegree)
  (hroot : ∀ p ∈ P, ∀ ρ ∈ S p, f.eval₂ (Int.castRingHom (ZMod p)) ρ = 0)
  (e : ∀ p : P, R ≃ S p.val)
  (s q D T : ℕ) (hs : 0 < s) (hsq : s < q) (hqk : q ≤ P.card) (hT : 2 ≤ T)
  (η g : ℝ) (hη : 0 < η) (hη1 : η ≤ 1) (hg : 0 < g)
  (hlo : ∀ p ∈ P, T ≤ p) (hhi : ∀ p ∈ P, p ≤ 2 * T)
  (θ L Lw : ℝ) (hθ : 0 < θ) (hL : 0 < L) (hN : Real.log (N + 1 : ℕ) ≤ Lw)
  (r : A → ℕ)
  (hstep : ∀ t, |(z (t + 1)).1 - (z t).1| ≤ D ∧ |(z (t + 1)).2 - (z t).2| ≤ D)
  (hinj : ∀ a, μ {a} ≠ 0 → ∀ i ≤ N, ∀ j ≤ N, z (b a + i) = z (b a + j) → i = j)
  (hr : ∀ a, μ {a} ≠ 0 → 0 < r a)
  (hsr : ∀ a, μ {a} ≠ 0 → s + roundedHarperCount (harperQuotaWidth η) (r a) ≤ P.card)
  (hbudget : ∀ a, μ {a} ≠ 0 →
    RoundedSubsetSeparationBudget f (fun k => z (b a + k)) D N P T (r a) η g)
  (hε : ∀ a, μ {a} ≠ 0 → roundedSubsetFailureBound P f.natDegree (r a) η g ≤ 1)
  (hnumeric : ∀ a, μ {a} ≠ 0 → θ * L ≤
    ((1 - roundedSubsetFailureBound P f.natDegree (r a) η g) *
        (Real.log (prefixArea (fun k => z (b a + k)) N : ℝ) -
          2 * Real.log (4 * D + 1 : ℕ)) - 2 * (s : ℝ) * Real.log (2 * T : ℕ)) /
      roundedHarperCount (harperQuotaWidth η) (r a))

include hf hd hP hcard hroot hs hsq hqk hT hη hη1 hg hlo hhi hθ hL hN
  hr hsr hbudget hε hnumeric hstep hinj

/-- Actual paired-source normalized enrichment with derived prime/root failure.
Only the displayed batch/geometric scalar budgets remain numeric inputs. -/
theorem rounded_prime_subset_paired_normalized_enrichment :
    (θ + labelledPointEntropyMean (fun p : P => ZMod p.val) (labelledPrimeResidue P S e)
      μ q (fun a => z (b a)) / ((q : ℝ) * L)) / 2 -
      (4 * Lw + 4 * Real.log (4 * D + 1 : ℕ) + 2 * (s : ℝ) * Real.log (2 * T : ℕ)) /
        (2 * (q - s : ℕ) * L) ≤
    labelledPointEntropyMean (fun p : P => ZMod p.val) (labelledPrimeResidue P S e)
      (fairEndpointLaw (differencePairForwardLaw z N μ b)) s
      (fairEndpointPoint (fun ω => z (differencePairFirstTime N b ω))
        (fun ω => z (differencePairSecondTime N b ω))) / ((s : ℝ) * L) := by
  have hqH : 0 < harperQuotaWidth η := by
    have h := (harperQuotaWidth_schedule η hη).1
    omega
  apply differencePairForwardLaw_scaled_normalized_enrichment z N μ b
    (fun p : P => ZMod p.val) (labelledPrimeResidue P S e) s q D T hs hsq
    (by simpa using hqk) θ L Lw hθ hL hN
    (fun a => roundedHarperCount (harperQuotaWidth η) (r a))
    (fun a => roundedSubsetFailureBound P f.natDegree (r a) η g) hstep hinj
  · intro a ha
    have h := (roundedHarperCount_bounds (harperQuotaWidth η) (r a) hqH).1
    have hp := hr a ha
    omega
  · intro a ha
    simpa using hsr a ha
  · intro p
    simpa using hhi p.val p.property
  · exact hε
  · intro a ha
    exact rounded_prime_subset_bad_fraction_le f hf hd (fun k => z (b a + k)) D N
      (fun t _ => by simpa [Nat.add_assoc] using hstep (b a + t)) P hP S hcard hroot e
      T (r a) hT (hr a ha) η g hη hη1 hg (by have h := hsr a ha; omega)
      hlo hhi (hbudget a ha)
  · exact hnumeric

/-- The same derived bound applies on positive ORIGINAL-base checkpoints;
conditioning is transported to the actual pair-plus-coin law. -/
theorem rounded_prime_subset_cond_paired_normalized_enrichment
    {B : Type*} [MeasurableSpace B] [MeasurableSingletonClass B]
    (V : A → B) (c : B) (hc : μ (V ⁻¹' {c}) ≠ 0) :
    (θ + labelledPointEntropyMean (fun p : P => ZMod p.val) (labelledPrimeResidue P S e)
      (μ[|V ⁻¹' {c}]) q (fun a => z (b a)) / ((q : ℝ) * L)) / 2 -
      (4 * Lw + 4 * Real.log (4 * D + 1 : ℕ) + 2 * (s : ℝ) * Real.log (2 * T : ℕ)) /
        (2 * (q - s : ℕ) * L) ≤
    labelledPointEntropyMean (fun p : P => ZMod p.val) (labelledPrimeResidue P S e)
      ((fairEndpointLaw (differencePairForwardLaw z N μ b))[|(fun ω => V ω.1.1) ⁻¹' {c}]) s
      (fairEndpointPoint (fun ω => z (differencePairFirstTime N b ω))
        (fun ω => z (differencePairSecondTime N b ω))) / ((s : ℝ) * L) := by
  let := cond_isProbabilityMeasure (μ := μ) (s := V ⁻¹' {c}) hc
  rw [differencePairFairLaw_cond_checkpoint z N μ b V c]
  apply rounded_prime_subset_paired_normalized_enrichment f hf hd z N (μ[|V ⁻¹' {c}]) b
    P hP S hcard hroot e s q D T hs hsq hqk hT η g hη hη1 hg hlo hhi
    θ L Lw hθ hL hN r hstep
  · intro a ha
    exact hinj a (cond_singleton_ne_zero_imp μ _ a ha)
  · intro a ha
    exact hr a (cond_singleton_ne_zero_imp μ _ a ha)
  · intro a ha
    exact hsr a (cond_singleton_ne_zero_imp μ _ a ha)
  · intro a ha
    exact hbudget a (cond_singleton_ne_zero_imp μ _ a ha)
  · intro a ha
    exact hε a (cond_singleton_ne_zero_imp μ _ a ha)
  · intro a ha
    exact hnumeric a (cond_singleton_ne_zero_imp μ _ a ha)

end Paired
end BinaryFormMoat.GeometryIntegration

#print axioms BinaryFormMoat.GeometryIntegration.rounded_prime_subset_uniformWalk_floor
#print axioms BinaryFormMoat.GeometryIntegration.rounded_prime_subset_paired_normalized_enrichment
#print axioms BinaryFormMoat.GeometryIntegration.rounded_prime_subset_cond_paired_normalized_enrichment
