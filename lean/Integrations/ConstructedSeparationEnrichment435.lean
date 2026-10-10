import Integrations.ConstructedSeparationError435
import Integrations.SubsetSeparationEnrichment435

noncomputable section
open scoped Classical
namespace BinaryFormMoat.GeometryIntegration
open HarperIntegration EntropyIntegration MeasureTheory ProbabilityTheory

/-- Primitive area-scale quotas, not an assumed separation/entropy inequality.
The paper's common schedule still has to establish these simultaneously. -/
structure ConstructedWalkEnrichmentQuota (f : Polynomial ℤ) (z : ℕ → Point)
    (D N : ℕ) (P : Finset ℕ) (T b : ℕ) (g : ℝ) : Prop where
  area_pos : 0 < walkSeparationAreaLog z N
  overhead : walkSeparationOverhead f z D N ≤ g * walkSeparationAreaLog z N
  rounding : (1 + 18 / g ^ 2) * primeBatchLogMean P ≤ g * walkSeparationAreaLog z N
  prefix_cost : 2 * Real.log (4 * D + 1 : ℕ) + 2 * (b : ℝ) * Real.log (2 * T : ℕ) ≤
    g * walkSeparationAreaLog z N
  prime_tail : 2 * (Real.log 2) ^ 2 ≤ g ^ 3 * walkSeparationAreaLog z N * primeBatchLogMean P
  root_tail : 1049760 * f.natDegree * primeBatchLogMean P * Real.log (2 / g) ≤
    g ^ 8 * walkSeparationAreaLog z N
  inventory : b + walkSeparationTarget f z D N P g + 2 * harperQuotaWidth g ≤ P.card

/-- Derive the integer count, inventory, both scalar separation budgets, failure
quota and explicit geometric scalar floor from primitive area-scale inputs. -/
theorem constructed_walk_enrichment_inputs (f : Polynomial ℤ) (hd : 1 ≤ f.natDegree)
    (z : ℕ → Point) (D N : ℕ) (P : Finset ℕ) (T b : ℕ) (g : ℝ)
    (hT : 2 ≤ T) (hPk : 0 < P.card) (hlo : ∀ p ∈ P, T ≤ p) (hhi : ∀ p ∈ P, p ≤ 2 * T)
    (hg : 0 < g) (hg8 : g < 1 / 8) (hquota : ConstructedWalkEnrichmentQuota f z D N P T b g) :
    let r := walkSeparationTarget f z D N P g
    let s := roundedHarperCount (harperQuotaWidth g) r
    0 < r ∧ b + s ≤ P.card ∧ RoundedSubsetSeparationBudget f z D N P T r g g ∧
      roundedSubsetFailureBound P f.natDegree r g g ≤ g ∧
      (1 - 8 * g) * primeBatchLogMean P ≤
        ((1 - roundedSubsetFailureBound P f.natDegree r g g) *
          (Real.log (prefixArea z N : ℝ) - 2 * Real.log (4 * D + 1 : ℕ)) -
          2 * (b : ℝ) * Real.log (2 * T : ℕ)) / s := by
  let r := walkSeparationTarget f z D N P g
  let s := roundedHarperCount (harperQuotaWidth g) r
  have hL := (primeBatchLogMean_dyadic_bounds P T hT hPk hlo hhi).1
  have hH := (walkSeparationOverhead_bounds f z D N).1
  have hq : 0 < harperQuotaWidth g := by
    have h := (harperQuotaWidth_schedule g hg).1
    omega
  have hr : 0 < r := walkSeparationTarget_pos f z D N P g hquota.area_pos hL (by linarith)
  have hs : 0 < s := hr.trans_le (roundedHarperCount_bounds _ r hq).1
  have hbr : b + s ≤ P.card := scaledSeparationCount_fits _ b P.card hq _ _ _ _ hquota.inventory
  have hbudget := constructed_walk_separation_budget f z D N P T g hT hPk hlo hhi hg hg8.le
  have hε : roundedSubsetFailureBound P f.natDegree r g g ≤ g :=
    constructed_subset_failure_le P f.natDegree hd _ _ g hquota.area_pos hH hL hg (by linarith)
      hquota.prime_tail hquota.root_tail
  have hround := harperQuota_rounding_cost g (primeBatchLogMean P) _ hg (by linarith) hL.le hquota.rounding
  have hcount : (s : ℝ) * primeBatchLogMean P ≤ (1 + 6 * g) * walkSeparationAreaLog z N :=
    scaledSeparationCount_density_upper _ hq _ _ _ _ hquota.area_pos hH hL hg.le hg8.le
      hquota.overhead hround
  refine ⟨hr, hbr, hbudget, hε, ?_⟩
  exact scalar_coordinate_floor_ge _ (2 * Real.log (4 * D + 1 : ℕ))
    (2 * (b : ℝ) * Real.log (2 * T : ℕ)) _ g _ s hquota.area_pos
    (mul_nonneg (by norm_num) (Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ 4 * D + 1))))
    hs hg8.le (roundedSubsetFailureBound_nonneg P f.natDegree r g g) hε hcount hquota.prefix_cost

/-- Actual geometric coordinate floor with a constructed count and a concrete
(1-8g)L lower bound. Neither separation nor the scalar floor is assumed. -/
theorem constructed_prime_subset_uniformWalk_floor {R : Type*} [Fintype R] [Nonempty R]
    (f : Polynomial ℤ) (hf : Irreducible f) (hd : 2 ≤ f.natDegree)
    (z : ℕ → Point) (D N b : ℕ)
    (hstep : ∀ t < N, |(z (t + 1)).1 - (z t).1| ≤ D ∧ |(z (t + 1)).2 - (z t).2| ≤ D)
    (hinj : ∀ i ≤ N, ∀ j ≤ N, z i = z j → i = j)
    (P : Finset ℕ) [∀ p : P, NeZero p.val] (hP : ∀ p ∈ P, p.Prime)
    (S : (p : ℕ) → Finset (ZMod p)) (hcard : ∀ p ∈ P, (S p).card = f.natDegree)
    (hroot : ∀ p ∈ P, ∀ ρ ∈ S p, f.eval₂ (Int.castRingHom (ZMod p)) ρ = 0)
    (e : ∀ p : P, R ≃ S p.val) (T : ℕ) (g : ℝ) (hT : 2 ≤ T) (hPk : 0 < P.card)
    (hg : 0 < g) (hg8 : g < 1 / 8) (hlo : ∀ p ∈ P, T ≤ p) (hhi : ∀ p ∈ P, p ≤ 2 * T)
    (hquota : ConstructedWalkEnrichmentQuota f z D N P T b g) :
    (1 - 8 * g) * primeBatchLogMean P ≤
      labelledPointDifferenceFloor (fun p : P => ZMod p.val) (labelledPrimeResidue P S e)
        (uniformOn (Set.univ : Set (WalkDifferences z N))) b
        (fun h => z (walkDifferenceTimes z N h).1.val)
        (fun h => z (walkDifferenceTimes z N h).2.val) / (Fintype.card P - b : ℕ) := by
  obtain ⟨hr, hbr, hbudget, hε, hfloor⟩ :=
    constructed_walk_enrichment_inputs f (by omega) z D N P T b g hT hPk hlo hhi hg hg8 hquota
  exact hfloor.trans (rounded_prime_subset_uniformWalk_floor f hf hd z D N b hstep hinj
    P hP S hcard hroot e T _ hT hr g g hg (by linarith) hg hbr hlo hhi hbudget
    (hε.trans (by linarith)))

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
  (g : ℝ) (hg : 0 < g) (hg8 : g < 1 / 8)
  (hlo : ∀ p ∈ P, T ≤ p) (hhi : ∀ p ∈ P, p ≤ 2 * T)
  (Lw : ℝ) (hN : Real.log (N + 1 : ℕ) ≤ Lw)
  (hstep : ∀ t, |(z (t + 1)).1 - (z t).1| ≤ D ∧ |(z (t + 1)).2 - (z t).2| ≤ D)
  (hinj : ∀ a, μ {a} ≠ 0 → ∀ i ≤ N, ∀ j ≤ N, z (b a + i) = z (b a + j) → i = j)
  (hquota : ∀ a, μ {a} ≠ 0 → ConstructedWalkEnrichmentQuota f (fun k => z (b a + k)) D N P T s g)
  (hphysical : 4 * Lw + 4 * Real.log (4 * D + 1 : ℕ) + 2 * (s : ℝ) * Real.log (2 * T : ℕ) ≤
    2 * g * (q - s : ℕ) * primeBatchLogMean P)

include hf hd hP hcard hroot hs hsq hqk hT hg hg8 hlo hhi hN hstep hinj hquota hphysical

/-- The actual paired law has a total one-step deficit at most 5g. Constructed
counts, separation, numeric floors and physical costs discharge the old inputs. -/
theorem constructed_prime_subset_paired_enrichment :
    (1 + labelledPointEntropyMean (fun p : P => ZMod p.val) (labelledPrimeResidue P S e)
      μ q (fun a => z (b a)) / ((q : ℝ) * primeBatchLogMean P)) / 2 - 5 * g ≤
    labelledPointEntropyMean (fun p : P => ZMod p.val) (labelledPrimeResidue P S e)
      (fairEndpointLaw (differencePairForwardLaw z N μ b)) s
      (fairEndpointPoint (fun ω => z (differencePairFirstTime N b ω))
        (fun ω => z (differencePairSecondTime N b ω))) / ((s : ℝ) * primeBatchLogMean P) := by
  have hPk : 0 < P.card := by omega
  have hL := (primeBatchLogMean_dyadic_bounds P T hT hPk hlo hhi).1
  have hinputs (a : A) (ha : μ {a} ≠ 0) :=
    constructed_walk_enrichment_inputs f (by omega) (fun k => z (b a + k)) D N P T s g
      hT hPk hlo hhi hg hg8 (hquota a ha)
  have hnorm := rounded_prime_subset_paired_normalized_enrichment f hf hd z N μ b
    P hP S hcard hroot e s q D T hs hsq hqk hT g g hg (by linarith) hg hlo hhi
    (1 - 8 * g) (primeBatchLogMean P) Lw (by linarith) hL hN
    (fun a => walkSeparationTarget f (fun k => z (b a + k)) D N P g) hstep hinj
    (fun a ha => (hinputs a ha).1) (fun a ha => (hinputs a ha).2.1)
    (fun a ha => (hinputs a ha).2.2.1)
    (fun a ha => ((hinputs a ha).2.2.2.1).trans (by linarith))
    (fun a ha => (hinputs a ha).2.2.2.2)
  have hden : 0 < 2 * (q - s : ℕ) * primeBatchLogMean P := by
    have hdiff : 0 < q - s := Nat.sub_pos_of_lt hsq
    positivity
  have hc : (4 * Lw + 4 * Real.log (4 * D + 1 : ℕ) +
      2 * (s : ℝ) * Real.log (2 * T : ℕ)) / (2 * (q - s : ℕ) * primeBatchLogMean P) ≤ g := by
    apply (div_le_iff₀ hden).mpr
    nlinarith [hphysical]
  linarith

/-- The derived 5g deficit also holds after any positive original-base checkpoint. -/
theorem constructed_prime_subset_cond_paired_enrichment
    {B : Type*} [MeasurableSpace B] [MeasurableSingletonClass B]
    (V : A → B) (c : B) (hc : μ (V ⁻¹' {c}) ≠ 0) :
    (1 + labelledPointEntropyMean (fun p : P => ZMod p.val) (labelledPrimeResidue P S e)
      (μ[|V ⁻¹' {c}]) q (fun a => z (b a)) / ((q : ℝ) * primeBatchLogMean P)) / 2 - 5 * g ≤
    labelledPointEntropyMean (fun p : P => ZMod p.val) (labelledPrimeResidue P S e)
      ((fairEndpointLaw (differencePairForwardLaw z N μ b))[|(fun ω => V ω.1.1) ⁻¹' {c}]) s
      (fairEndpointPoint (fun ω => z (differencePairFirstTime N b ω))
        (fun ω => z (differencePairSecondTime N b ω))) / ((s : ℝ) * primeBatchLogMean P) := by
  let := cond_isProbabilityMeasure (μ := μ) (s := V ⁻¹' {c}) hc
  rw [differencePairFairLaw_cond_checkpoint z N μ b V c]
  apply constructed_prime_subset_paired_enrichment f hf hd z N (μ[|V ⁻¹' {c}]) b
    P hP S hcard hroot e s q D T hs hsq hqk hT g hg hg8 hlo hhi Lw hN hstep
  · intro a ha
    exact hinj a (cond_singleton_ne_zero_imp μ _ a ha)
  · intro a ha
    exact hquota a (cond_singleton_ne_zero_imp μ _ a ha)
  · exact hphysical

end Paired
end BinaryFormMoat.GeometryIntegration

#print axioms BinaryFormMoat.GeometryIntegration.ConstructedWalkEnrichmentQuota
#print axioms BinaryFormMoat.GeometryIntegration.constructed_walk_enrichment_inputs
#print axioms BinaryFormMoat.GeometryIntegration.constructed_prime_subset_uniformWalk_floor
#print axioms BinaryFormMoat.GeometryIntegration.constructed_prime_subset_paired_enrichment
#print axioms BinaryFormMoat.GeometryIntegration.constructed_prime_subset_cond_paired_enrichment
