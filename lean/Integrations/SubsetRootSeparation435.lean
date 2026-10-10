import Integrations.PrimeSubsetLabels435
import Integrations.RoundedHarperQuota435
import Integrations.SubsetPrimeProduct435

noncomputable section
open scoped Classical
namespace BinaryFormMoat.GeometryIntegration
open EntropyIntegration HarperIntegration

/-- The actual mean of the distinct prime batch, retained at small margins. -/
def primeBatchLogMean (P : Finset ℕ) : ℝ :=
  (∑ p : P, Real.log (p.val : ℝ)) / P.card

/-- Without-replacement prime tail plus conditional rounded-Harper root tail. -/
def roundedSubsetFailureBound (P : Finset ℕ) (d r : ℕ) (η g : ℝ) : ℝ :=
  (Real.log 2) ^ 2 /
      (g ^ 2 * roundedHarperCount (harperQuotaWidth η) r * (primeBatchLogMean P) ^ 2) +
    Real.exp (-(η ^ 8 * r) / (1049760 * d))

/-- Two batch scalar inequalities imply the arithmetic requirements of EVERY
subset whose log-product exceeds the exceptional threshold. -/
structure RoundedSubsetSeparationBudget (f : Polynomial ℤ) (z : ℕ → Point)
    (D N : ℕ) (P : Finset ℕ) (T r : ℕ) (η g : ℝ) : Prop where
  log_gap : Real.log (max 1 (4 * (D * N)) : ℕ) +
    Real.log (coefficientBound f f.natDegree : ℝ) / f.natDegree +
    η * roundedHarperCount (harperQuotaWidth η) r * Real.log (T : ℝ) ≤
      (1 - g) * roundedHarperCount (harperQuotaWidth η) r * primeBatchLogMean P
  log_product : Real.log (16 * prefixArea z N : ℕ) +
    (2 * roundedHarperBlocks (harperQuotaWidth η) r : ℕ) * Real.log (2 * T : ℕ) ≤
      (1 - g) * roundedHarperCount (harperQuotaWidth η) r * primeBatchLogMean P

theorem primeSubset_log_product (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    (J : Finset P) :
    Real.log ((∏ p ∈ primeSubset P J, p : ℕ) : ℝ) =
      ∑ p ∈ J, Real.log (p.val : ℝ) := by
  rw [Nat.cast_prod, Real.log_prod]
  · exact primeSubset_sum P J (fun p => Real.log (p : ℝ))
  · intro p hp
    exact_mod_cast (hP p (primeSubset_subset P J hp)).ne_zero

theorem primeSubset_product_of_log_budget (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    (J : Finset P) (M U a : ℕ) (hM : 0 < M) (hU : 0 < U) (B : ℝ)
    (hb : Real.log (M : ℝ) + (a : ℝ) * Real.log (U : ℝ) ≤ B)
    (hgood : B < ∑ p ∈ J, Real.log (p.val : ℝ)) :
    M * U ^ a < ∏ p ∈ primeSubset P J, p := by
  have hp : 0 < ∏ p ∈ primeSubset P J, p :=
    Finset.prod_pos (fun p hp => (hP p (primeSubset_subset P J hp)).pos)
  have hmR : (0 : ℝ) < M := by exact_mod_cast hM
  have huR : (0 : ℝ) < U := by exact_mod_cast hU
  have he : Real.log ((M * U ^ a : ℕ) : ℝ) =
      Real.log (M : ℝ) + (a : ℝ) * Real.log (U : ℝ) := by
    rw [Nat.cast_mul, Nat.cast_pow, Real.log_mul hmR.ne' (pow_ne_zero _ huR.ne'),
      Real.log_pow]
  have hl : Real.log ((M * U ^ a : ℕ) : ℝ) <
      Real.log ((∏ p ∈ primeSubset P J, p : ℕ) : ℝ) := by
    rw [he, primeSubset_log_product P hP J]
    exact hb.trans_lt hgood
  have hr := (Real.log_lt_log_iff (by positivity : (0 : ℝ) < (M * U ^ a : ℕ))
    (by exact_mod_cast hp)).mp hl
  exact_mod_cast hr

/-- Actual uniform subset/global-root-label collision fraction. No failure
fraction is assumed: it follows from two scalar batch budgets and both tails. -/
theorem rounded_prime_subset_bad_fraction_le {R : Type*} [Fintype R] [Nonempty R]
    (f : Polynomial ℤ) (hf : Irreducible f) (hd : 2 ≤ f.natDegree)
    (z : ℕ → Point) (D N : ℕ)
    (hstep : ∀ t < N, |(z (t + 1)).1 - (z t).1| ≤ D ∧ |(z (t + 1)).2 - (z t).2| ≤ D)
    (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    (S : (p : ℕ) → Finset (ZMod p)) (hcard : ∀ p ∈ P, (S p).card = f.natDegree)
    (hroot : ∀ p ∈ P, ∀ ρ ∈ S p, f.eval₂ (Int.castRingHom (ZMod p)) ρ = 0)
    (e : ∀ p : P, R ≃ S p.val) (T r : ℕ) (hT : 2 ≤ T) (hr : 0 < r)
    (η g : ℝ) (hη : 0 < η) (hη1 : η ≤ 1) (hg : 0 < g)
    (hsk : roundedHarperCount (harperQuotaWidth η) r ≤ P.card)
    (hlo : ∀ p ∈ P, T ≤ p) (hhi : ∀ p ∈ P, p ≤ 2 * T)
    (hbudget : RoundedSubsetSeparationBudget f z D N P T r η g) :
    badLabelledSubsetFraction (fun p : P => ZMod p.val)
      (fun p a => labelledPrimeResidue P S e p a)
      (pointDifferences (walkVertexSet z N)) (roundedHarperCount (harperQuotaWidth η) r) ≤
        roundedSubsetFailureBound P f.natDegree r η g := by
  classical
  let : DecidableEq P := Classical.decEq P
  let : ∀ p : P, NeZero p.val := fun p => ⟨(hP p.val p.property).ne_zero⟩
  let s := roundedHarperCount (harperQuotaWidth η) r
  have hq : 0 < harperQuotaWidth η := by
    have h := (harperQuotaWidth_schedule η hη).1
    omega
  have hs : 2 ≤ s := by
    have hb := roundedHarperBlocks_pos (harperQuotaWidth η) r hq hr
    dsimp [s, roundedHarperCount]
    nlinarith [hq]
  rw [badLabelledSubsetFraction_eq_indicator_mean]
  convert finite_fiber_failure_mean_le (ι := P) (R := R) s
    (fun J => (∑ p ∈ J, Real.log (p.val : ℝ)) ≤ (1 - g) * s * primeBatchLogMean P)
    (fun J ρ => ¬ Set.InjOn
      (labelledSubsetProjection (fun p : P => ZMod p.val)
        (fun p a => labelledPrimeResidue P S e p a) J ρ)
      (pointDifferences (walkVertexSet z N) : Set Point))
    ((Real.log 2) ^ 2 / (g ^ 2 * s * (primeBatchLogMean P) ^ 2))
    (Real.exp (-(η ^ 8 * r) / (1049760 * f.natDegree))) (Real.exp_pos _).le ?_ ?_ using 1
  · congr 1
    funext J ρ
    congr 1
  · rfl
  · exact subsetLabelAverage_prime_log_failure_le (R := R) P T s hT hs hsk hlo hhi g hg
  · intro J hJ hgood
    have hjcard : (primeSubset P J).card = s :=
      (primeSubset_card P J).trans (Finset.mem_powersetCard.mp hJ).2
    have hstrict : (1 - g) * s * primeBatchLogMean P <
        ∑ p ∈ J, Real.log (p.val : ℝ) := lt_of_not_ge hgood
    have hgap : Real.log (max 1 (4 * (D * N)) : ℕ) +
        Real.log (coefficientBound f f.natDegree : ℝ) / f.natDegree +
        η * (primeSubset P J).card * Real.log (T : ℝ) ≤
          ∑ p ∈ primeSubset P J, Real.log (p : ℝ) := by
      rw [hjcard, primeSubset_sum]
      exact hbudget.log_gap.trans hstrict.le
    have hlarge : (16 * prefixArea z N) *
        (2 * T) ^ (2 * roundedHarperBlocks (harperQuotaWidth η) r) <
          ∏ p ∈ primeSubset P J, p :=
      primeSubset_product_of_log_budget P hP J _ _ _
        (by have h := prefixArea_pos z N; positivity) (by omega) _
        hbudget.log_product hstrict
    rw [global_prime_projection_bad_fraction]
    exact walk_difference_separation_rounded_rate f hf hd z D N hstep (primeSubset P J)
      (fun p hp => hP p (primeSubset_subset P J hp)) S
      (fun p hp => hcard p (primeSubset_subset P J hp))
      (fun p hp => hroot p (primeSubset_subset P J hp)) r hr η hη hη1 hjcard T hT
      (fun p hp => hhi p (primeSubset_subset P J hp)) hgap hlarge

end BinaryFormMoat.GeometryIntegration

#print axioms BinaryFormMoat.GeometryIntegration.primeBatchLogMean
#print axioms BinaryFormMoat.GeometryIntegration.roundedSubsetFailureBound
#print axioms BinaryFormMoat.GeometryIntegration.RoundedSubsetSeparationBudget
#print axioms BinaryFormMoat.GeometryIntegration.primeSubset_log_product
#print axioms BinaryFormMoat.GeometryIntegration.primeSubset_product_of_log_budget
#print axioms BinaryFormMoat.GeometryIntegration.rounded_prime_subset_bad_fraction_le
