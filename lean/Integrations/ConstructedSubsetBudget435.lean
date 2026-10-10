import Integrations.ScaledSeparationCount435
import Integrations.SubsetRootSeparation435

noncomputable section
namespace BinaryFormMoat.GeometryIntegration
open EntropyIntegration HarperIntegration

def walkSeparationAreaLog (z : ℕ → Point) (N : ℕ) : ℝ := Real.log (prefixArea z N : ℝ)

def walkSeparationRadiusLog (f : Polynomial ℤ) (D N : ℕ) : ℝ :=
  Real.log (max 1 (4 * (D * N)) : ℕ) +
    Real.log (coefficientBound f f.natDegree : ℝ) / f.natDegree

def walkSeparationOverhead (f : Polynomial ℤ) (z : ℕ → Point) (D N : ℕ) : ℝ :=
  max (Real.log 16) (walkSeparationRadiusLog f D N - walkSeparationAreaLog z N)

def walkSeparationTarget (f : Polynomial ℤ) (z : ℕ → Point) (D N : ℕ)
    (P : Finset ℕ) (g : ℝ) : ℕ :=
  scaledSeparationTarget (walkSeparationAreaLog z N) (walkSeparationOverhead f z D N)
    (primeBatchLogMean P) g

/-- The actual dyadic batch has positive true mean; only a fixed-factor bound
on log(2T) is used, with no log(2)<=g*log(T) premise. -/
theorem primeBatchLogMean_dyadic_bounds (P : Finset ℕ) (T : ℕ) (hT : 2 ≤ T)
    (hPk : 0 < P.card) (hlo : ∀ p ∈ P, T ≤ p) (hhi : ∀ p ∈ P, p ≤ 2 * T) :
    0 < primeBatchLogMean P ∧ Real.log (T : ℝ) ≤ primeBatchLogMean P ∧
      primeBatchLogMean P ≤ Real.log (2 * T : ℕ) ∧
      Real.log (2 * T : ℕ) ≤ 2 * primeBatchLogMean P := by
  have hTpos : (0 : ℝ) < T := by exact_mod_cast (by omega : 0 < T)
  have hp (p : P) : (0 : ℝ) < p.val :=
    hTpos.trans_le (by exact_mod_cast hlo p.val p.property)
  have hb := finite_real_mean_bounds (ι := P) (by simpa using hPk)
    (fun p => Real.log (p.val : ℝ)) (Real.log (T : ℝ)) (Real.log (2 * T : ℕ))
    (fun p => ⟨Real.log_le_log hTpos (by exact_mod_cast hlo p.val p.property),
      Real.log_le_log (hp p) (by exact_mod_cast hhi p.val p.property)⟩)
  have hl : Real.log (T : ℝ) ≤ primeBatchLogMean P := by
    simpa [primeBatchLogMean] using hb.1
  have hu : primeBatchLogMean P ≤ Real.log (2 * T : ℕ) := by
    simpa [primeBatchLogMean] using hb.2
  have ht : 0 < Real.log (T : ℝ) := Real.log_pos (by exact_mod_cast (by omega : 1 < T))
  have htwo : Real.log 2 ≤ Real.log (T : ℝ) :=
    Real.log_le_log (by norm_num) (by exact_mod_cast hT)
  have he : Real.log (2 * T : ℕ) = Real.log 2 + Real.log (T : ℝ) := by
    rw [Nat.cast_mul, Nat.cast_ofNat, Real.log_mul (by norm_num) hTpos.ne']
  exact ⟨ht.trans_le hl, hl, hu, by rw [he]; linarith⟩

theorem walkSeparationOverhead_bounds (f : Polynomial ℤ) (z : ℕ → Point) (D N : ℕ) :
    0 ≤ walkSeparationOverhead f z D N ∧
      walkSeparationRadiusLog f D N ≤ walkSeparationAreaLog z N + walkSeparationOverhead f z D N ∧
      Real.log (16 * prefixArea z N : ℕ) ≤ walkSeparationAreaLog z N + walkSeparationOverhead f z D N := by
  have h16 := le_max_left (Real.log 16)
    (walkSeparationRadiusLog f D N - walkSeparationAreaLog z N)
  have hr := le_max_right (Real.log 16)
    (walkSeparationRadiusLog f D N - walkSeparationAreaLog z N)
  have h0 : 0 ≤ Real.log 16 := Real.log_nonneg (by norm_num)
  have harea : (prefixArea z N : ℝ) ≠ 0 := by exact_mod_cast (prefixArea_pos z N).ne'
  have he : Real.log (16 * prefixArea z N : ℕ) = Real.log 16 + walkSeparationAreaLog z N := by
    rw [Nat.cast_mul, Nat.cast_ofNat, Real.log_mul (by norm_num) harea]
    rfl
  exact ⟨h0.trans h16, by dsimp [walkSeparationOverhead]; linarith,
    by rw [he]; dsimp [walkSeparationOverhead]; linarith⟩

/-- A fixed f,D overhead works for every walk, base point and window length. -/
def walkSeparationFixedOverhead (f : Polynomial ℤ) (D : ℕ) : ℝ :=
  max (Real.log 16) (Real.log (max 1 (4 * D) : ℕ) +
    Real.log (coefficientBound f f.natDegree : ℝ) / f.natDegree)

theorem walkSeparationOverhead_le_fixed (f : Polynomial ℤ) (z : ℕ → Point) (D N : ℕ) :
    walkSeparationOverhead f z D N ≤ walkSeparationFixedOverhead f D := by
  have ha : N + 1 ≤ prefixArea z N := le_max_left _ _
  have hm : 1 ≤ max 1 (4 * D) := le_max_left _ _
  have hrad : max 1 (4 * (D * N)) ≤ max 1 (4 * D) * prefixArea z N := by
    apply max_le
    · have hA : 1 ≤ prefixArea z N := by omega
      nlinarith
    · calc
        _ = (4 * D) * N := by ring
        _ ≤ max 1 (4 * D) * (N + 1) := Nat.mul_le_mul (le_max_right _ _) (Nat.le_succ N)
        _ ≤ _ := Nat.mul_le_mul_left _ ha
  have hradR : ((max 1 (4 * (D * N)) : ℕ) : ℝ) ≤
      ((max 1 (4 * D) * prefixArea z N : ℕ) : ℝ) := by exact_mod_cast hrad
  have hl := Real.log_le_log
    (show (0 : ℝ) < (max 1 (4 * (D * N)) : ℕ) by positivity)
    hradR
  have he : Real.log (max 1 (4 * D) * prefixArea z N : ℕ) =
      Real.log (max 1 (4 * D) : ℕ) + walkSeparationAreaLog z N := by
    rw [Nat.cast_mul, Real.log_mul (by positivity)
      (by exact_mod_cast (prefixArea_pos z N).ne')]
    rfl
  rw [he] at hl
  unfold walkSeparationOverhead walkSeparationFixedOverhead
  apply max_le (le_max_left _ _)
  apply le_trans _ (le_max_right _ _)
  unfold walkSeparationRadiusLog
  linarith

/-- The integer Harper width makes each block's determinant cost small. -/
theorem harperQuota_product_cost_le (r : ℕ) (g L U : ℝ) (hg : 0 < g) (hg1 : g ≤ 1)
    (hL : 0 ≤ L) (hU : U ≤ 2 * L) :
    (2 * roundedHarperBlocks (harperQuotaWidth g) r : ℕ) * U ≤
      g * roundedHarperCount (harperQuotaWidth g) r * L := by
  have hqR : (0 : ℝ) ≤ harperQuotaWidth g := Nat.cast_nonneg _
  have hs := (harperQuotaWidth_schedule g hg).2
  have hg2 : g ^ 2 ≤ g := by nlinarith
  have hm := mul_le_mul_of_nonneg_right hg2 hqR
  have hq : 2 ≤ g * harperQuotaWidth g := by linarith
  calc
    _ ≤ (2 * roundedHarperBlocks (harperQuotaWidth g) r : ℕ) * (2 * L) := by gcongr
    _ ≤ (2 * roundedHarperBlocks (harperQuotaWidth g) r : ℕ) *
        ((g * harperQuotaWidth g) * L) := by gcongr
    _ = _ := by simp only [roundedHarperCount, Nat.cast_mul, Nat.cast_ofNat]; ring

theorem walkSeparationTarget_pos (f : Polynomial ℤ) (z : ℕ → Point) (D N : ℕ)
    (P : Finset ℕ) (g : ℝ) (hA : 0 < walkSeparationAreaLog z N)
    (hL : 0 < primeBatchLogMean P) (hg : g < 1 / 2) :
    0 < walkSeparationTarget f z D N P g :=
  scaledSeparationTarget_pos _ _ _ _ hA (walkSeparationOverhead_bounds f z D N).1 hL hg

/-- Construct BOTH former scalar separation hypotheses by choosing a target
count. Small-overhead/density and inventory conditions are separate later quotas. -/
theorem constructed_walk_separation_budget (f : Polynomial ℤ) (z : ℕ → Point) (D N : ℕ)
    (P : Finset ℕ) (T : ℕ) (g : ℝ) (hT : 2 ≤ T) (hPk : 0 < P.card)
    (hlo : ∀ p ∈ P, T ≤ p) (hhi : ∀ p ∈ P, p ≤ 2 * T)
    (hg : 0 < g) (hg8 : g ≤ 1 / 8) :
    RoundedSubsetSeparationBudget f z D N P T (walkSeparationTarget f z D N P g) g g := by
  let r := walkSeparationTarget f z D N P g
  let s := roundedHarperCount (harperQuotaWidth g) r
  have hb := primeBatchLogMean_dyadic_bounds P T hT hPk hlo hhi
  have hH := walkSeparationOverhead_bounds f z D N
  have hq : 0 < harperQuotaWidth g := by
    have h := (harperQuotaWidth_schedule g hg).1
    omega
  have hl : walkSeparationAreaLog z N + walkSeparationOverhead f z D N ≤
      (1 - 2 * g) * s * primeBatchLogMean P :=
    scaledSeparationCount_log_lower _ hq _ _ _ _ hb.1 (by linarith)
  have hTcost : g * s * Real.log (T : ℝ) ≤ g * s * primeBatchLogMean P := by gcongr; exact hb.2.1
  have hprod := harperQuota_product_cost_le r g (primeBatchLogMean P) (Real.log (2 * T : ℕ))
    hg (by linarith) hb.1.le hb.2.2.2
  constructor
  · change walkSeparationRadiusLog f D N + g * s * Real.log (T : ℝ) ≤
      (1 - g) * s * primeBatchLogMean P
    nlinarith [hH.2.1]
  · change Real.log (16 * prefixArea z N : ℕ) +
      (2 * roundedHarperBlocks (harperQuotaWidth g) r : ℕ) * Real.log (2 * T : ℕ) ≤
      (1 - g) * s * primeBatchLogMean P
    change _ ≤ g * s * primeBatchLogMean P at hprod
    nlinarith [hH.2.2]

end BinaryFormMoat.GeometryIntegration

#print axioms BinaryFormMoat.GeometryIntegration.walkSeparationAreaLog
#print axioms BinaryFormMoat.GeometryIntegration.walkSeparationRadiusLog
#print axioms BinaryFormMoat.GeometryIntegration.walkSeparationOverhead
#print axioms BinaryFormMoat.GeometryIntegration.walkSeparationTarget
#print axioms BinaryFormMoat.GeometryIntegration.primeBatchLogMean_dyadic_bounds
#print axioms BinaryFormMoat.GeometryIntegration.walkSeparationOverhead_bounds
#print axioms BinaryFormMoat.GeometryIntegration.walkSeparationFixedOverhead
#print axioms BinaryFormMoat.GeometryIntegration.walkSeparationOverhead_le_fixed
#print axioms BinaryFormMoat.GeometryIntegration.harperQuota_product_cost_le
#print axioms BinaryFormMoat.GeometryIntegration.walkSeparationTarget_pos
#print axioms BinaryFormMoat.GeometryIntegration.constructed_walk_separation_budget
