import Moat.RotatedRectangles
import Integrations.RectangleHarper435

namespace BinaryFormMoat.HarperIntegration

/-- Radius controls the polynomial tail, while determinant size controls packing. -/
theorem harper_finiteSet_bound (f : Polynomial ℤ) (hf : Irreducible f)
    (hd : 2 ≤ f.natDegree)
    (E : Finset Point) (R M : ℕ)
    (hradius : ∀ z ∈ E, max z.1.natAbs z.2.natAbs ≤ R)
    (hdet : ∀ z ∈ E, ∀ w ∈ E, (determinant z w).natAbs ≤ M)
    (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    (S : (p : ℕ) → Finset (ZMod p)) (hcard : ∀ p ∈ P, (S p).card = f.natDegree)
    (hroot : ∀ p ∈ P, ∀ ρ ∈ S p, f.eval₂ (Int.castRingHom (ZMod p)) ρ = 0)
    (b q l : ℕ) (hb : 2 * f.natDegree ≤ 2 ^ b) (hm : 2 ≤ b * q) (hl : 1 ≤ l)
    (hcount : P.card = 2 * q * l)
    (T : ℕ) (hT : 2 ≤ T) (hpT : ∀ p ∈ P, p ≤ 2 * T) (η : ℝ) (hη : 0 ≤ η)
    (hschedule : 3 ≤ (η ^ 2 / 2) * q)
    (hgap : Real.log (R : ℝ) +
      Real.log (coefficientBound f f.natDegree : ℝ) / f.natDegree +
      η * P.card * Real.log (T : ℝ) ≤ ∑ p ∈ P, Real.log (p : ℝ))
    (hlarge : M * (2 * T) ^ (2 * l) < ∏ p ∈ P, p) :
    ((finiteSetWitnessEvent E P S).card : ℝ) / Fintype.card (∀ p : P, S p) ≤
      Real.exp (2 * (f.natDegree : ℝ) / 2 ^ b * P.card) /
        rectangleGrowthFactor b q l ^ l := by
  classical
  have hq : 0 < q := by
    by_contra h
    have hq0 : q = 0 := by omega
    rw [hq0, mul_zero] at hm
    omega
  have hne : P.Nonempty := Finset.card_pos.mp (by rw [hcount]; positivity)
  have hK : ∀ p : P, Fintype.card (S p) = f.natDegree :=
    fun p => by simpa using hcard p p.property
  let e : ∀ p : P, (S p) × Fin (2 ^ b / f.natDegree) ↪ (Fin b → Bool) :=
    fun p => Classical.choice (exists_balanced_binary_embedding (S p) f.natDegree b (hK p))
  have hdim : Fintype.card (P × Fin b) = 2 * (b * q) * l := by
    simp only [Fintype.card_prod, Fintype.card_coe, Fintype.card_fin, hcount]
    ring
  have hg : 0 < rectangleGrowthFactor b q l := by
    have h := (scheduled_factor_bounds (b * q : ℕ) l
      (by exact_mod_cast hm) (by exact_mod_cast hl)).1
    have hp : (0 : ℝ) < 1 + 1 / (b * q : ℕ) := by positivity
    exact hp.trans_le h
  rw [← Fintype.card_coe P]
  apply balanced_encoding_transfer f.natDegree b (by omega) hb hK e _ _ (pow_pos hg l)
  apply encoded_finiteSet_packing E R M hradius hdet P hP S b (2 ^ b / f.natDegree) e (2 * T) l
    (by omega) hpT hlarge _ (by positivity)
  intro z hz
  have htail := encoded_finiteSet_irreducible_line_tail f hf hd E R hradius P hP hne S hcard hroot
    b (2 ^ b / f.natDegree) e T hT hpT η hη hgap z hz
  have hA : ((encodedBitEvent b e (finiteSetRootWitnessEvent E P S z)).card : ℝ) /
      2 ^ Fintype.card (P × Fin b) ≤ Real.exp (-(η ^ 2 / 2) * (2 * q * l)) := by
    simpa only [Fintype.card_fun, Fintype.card_bool, hcount, Nat.cast_mul,
      Nat.cast_pow, Nat.cast_ofNat, neg_mul, neg_div, div_mul_eq_mul_div] using htail
  exact scheduled_harper_expansion (b * q) q l hm hl hdim (η ^ 2 / 2)
    hschedule _ hA

/-- A deliberately coarse block width makes the all-line estimate decay at
a definite rate after the exact-balancing penalty. The prime and rectangle
conditions remain explicit; they are not consequences of Harper alone. -/
theorem harper_finiteSet_exp_tail (f : Polynomial ℤ) (hf : Irreducible f)
    (hd : 2 ≤ f.natDegree)
    (E : Finset Point) (R M : ℕ)
    (hradius : ∀ z ∈ E, max z.1.natAbs z.2.natAbs ≤ R)
    (hdet : ∀ z ∈ E, ∀ w ∈ E, (determinant z w).natAbs ≤ M)
    (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    (S : (p : ℕ) → Finset (ZMod p)) (hcard : ∀ p ∈ P, (S p).card = f.natDegree)
    (hroot : ∀ p ∈ P, ∀ ρ ∈ S p, f.eval₂ (Int.castRingHom (ZMod p)) ρ = 0)
    (q l : ℕ) (hq : 0 < q) (hl : 1 ≤ l) (hcount : P.card = 2 * q * l)
    (T : ℕ) (hT : 2 ≤ T) (hpT : ∀ p ∈ P, p ≤ 2 * T) (η : ℝ) (hη : 0 ≤ η)
    (hschedule : 3 ≤ (η ^ 2 / 2) * q)
    (hgap : Real.log (R : ℝ) +
      Real.log (coefficientBound f f.natDegree : ℝ) / f.natDegree +
      η * P.card * Real.log (T : ℝ) ≤ ∑ p ∈ P, Real.log (p : ℝ))
    (hlarge : M * (2 * T) ^ (2 * l) < ∏ p ∈ P, p) :
    let b := 16 * f.natDegree * q ^ 2 + 4
    ((finiteSetWitnessEvent E P S).card : ℝ) / Fintype.card (∀ p : P, S p) ≤
      Real.exp (-(l : ℝ) / (4 * (b * q : ℕ))) := by
  dsimp
  let b := 16 * f.natDegree * q ^ 2 + 4
  obtain ⟨hm, hb, hQ⟩ := explicit_balanced_growth_block f.natDegree q hq
  change 2 ≤ b * q at hm
  change 2 * f.natDegree ≤ 2 ^ b at hb
  change 16 * f.natDegree * (b * q) * q ≤ 2 ^ b at hQ
  have hbound := harper_finiteSet_bound f hf hd E R M hradius hdet P hP S hcard hroot b q l hb hm hl
    hcount T hT hpT η hη hschedule hgap hlarge
  have hg : 0 < rectangleGrowthFactor b q l := by
    have h := (scheduled_factor_bounds (b * q : ℕ) l
      (by exact_mod_cast hm) (by exact_mod_cast hl)).1
    have hp : (0 : ℝ) < 1 + 1 / (b * q : ℕ) := by positivity
    exact hp.trans_le h
  have he : rectangleGrowthFactor b q l ^ l =
      Real.exp ((l : ℝ) * Real.log (rectangleGrowthFactor b q l)) := by
    rw [Real.exp_nat_mul, Real.exp_log hg]
  rw [he, ← Real.exp_sub] at hbound
  apply hbound.trans
  apply Real.exp_le_exp.mpr
  have hgain := scheduled_net_gain (b * q : ℕ) l f.natDegree q (2 ^ b : ℕ)
    (by exact_mod_cast hm) (by exact_mod_cast hl) (by exact_mod_cast (by omega : 0 < f.natDegree))
    (by exact_mod_cast hq) (by exact_mod_cast hQ)
  have hgain' : (l : ℝ) / (4 * (b * q : ℕ)) ≤
    (l : ℝ) * Real.log (rectangleGrowthFactor b q l) -
      2 * f.natDegree / (2 : ℝ) ^ b * (2 * q * l) := by
    simpa only [rectangleGrowthFactor, Nat.cast_pow, Nat.cast_ofNat] using hgain
  rw [hcount]
  dsimp only [b] at hgain' ⊢
  push_cast at hgain' ⊢
  simpa only [neg_sub, neg_div] using neg_le_neg hgain'

/-- Arbitrary real orientation preserves the area budget. Integer-coordinate
root equations and radius A+B avoid rotating the polynomial itself. -/
theorem harper_rotated_rectangle_exp_tail_of_dyadic_bounds
    (f : Polynomial ℤ) (hf : Irreducible f) (hd : 2 ≤ f.natDegree)
    (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    (S : (p : ℕ) → Finset (ZMod p)) (hcard : ∀ p ∈ P, (S p).card = f.natDegree)
    (hroot : ∀ p ∈ P, ∀ ρ ∈ S p, f.eval₂ (Int.castRingHom (ZMod p)) ρ = 0)
    (q l : ℕ) (hq : 2 ≤ q) (hl : 1 ≤ l) (hcount : P.card = 2 * q * l)
    (a b : ℝ) (hab : a ^ 2 + b ^ 2 = 1) (A B T : ℕ)
    (hT : 2 ≤ T) (hlo : ∀ p ∈ P, T ≤ p) (hhi : ∀ p ∈ P, p ≤ 2 * T)
    (η : ℝ) (hη : 0 ≤ η) (hschedule : 3 ≤ (η ^ 2 / 2) * q)
    (hsize : Real.log ((A + B : ℕ) : ℝ) +
      Real.log (coefficientBound f f.natDegree : ℝ) / f.natDegree ≤
      (1 - η) * P.card * Real.log (T : ℝ))
    (harea : 2 * A * B < T ^ ((2 * q - 4) * l)) :
    let w := 16 * f.natDegree * q ^ 2 + 4
    ((finiteSetWitnessEvent (rotatedRectanglePoints a b A B) P S).card : ℝ) /
      Fintype.card (∀ p : P, S p) ≤ Real.exp (-(l : ℝ) / (4 * (w * q : ℕ))) :=
  harper_finiteSet_exp_tail f hf hd (rotatedRectanglePoints a b A B) (A + B) (2 * A * B)
    (rotatedRectangle_radius a b A B) (rotatedRectangle_determinant_bound a b hab A B)
    P hP S hcard hroot q l (by omega) hl hcount T hT hhi η hη hschedule
    (rectangle_log_gap_of_dyadic_lower P T (by omega) hlo _ η hsize)
    (rectangle_separation_of_dyadic_bounds P T q l A B hT hq hcount hlo harea)

end BinaryFormMoat.HarperIntegration
