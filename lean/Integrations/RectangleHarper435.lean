import Moat.RectanglePacking
import Moat.RectangleParameters
import Integrations.HarperSchedule435

namespace BinaryFormMoat.HarperIntegration

noncomputable def rectangleGrowthFactor (b q l : ℕ) : ℝ :=
  ((((b * q : ℕ) : ℝ) + 1) * l) / ((((b * q : ℕ) : ℝ) - 1) * l + 1)

/-- The all-line rectangle estimate has only arithmetic and scalar parameter
conditions. Finite representatives, encoding, expansion and packing are all
constructed in the proof. The event includes every nonzero integer point. -/
theorem harper_rectangle_bound (f : Polynomial ℤ) (hf : Irreducible f)
    (hd : 2 ≤ f.natDegree)
    (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    (S : (p : ℕ) → Finset (ZMod p)) (hcard : ∀ p ∈ P, (S p).card = f.natDegree)
    (hroot : ∀ p ∈ P, ∀ ρ ∈ S p, f.eval₂ (Int.castRingHom (ZMod p)) ρ = 0)
    (b q l : ℕ) (hb : 2 * f.natDegree ≤ 2 ^ b) (hm : 2 ≤ b * q) (hl : 1 ≤ l)
    (hcount : P.card = 2 * q * l)
    (A B T : ℕ) (hT : 2 ≤ T) (hpT : ∀ p ∈ P, p ≤ 2 * T) (η : ℝ) (hη : 0 ≤ η)
    (hschedule : 3 ≤ (η ^ 2 / 2) * q)
    (hgap : Real.log ((max A B : ℕ) : ℝ) +
      Real.log (coefficientBound f f.natDegree : ℝ) / f.natDegree +
      η * P.card * Real.log (T : ℝ) ≤ ∑ p ∈ P, Real.log (p : ℝ))
    (hlarge : (2 * A * B) * (2 * T) ^ (2 * l) < ∏ p ∈ P, p) :
    ((rectangleWitnessEvent P S A B).card : ℝ) / Fintype.card (∀ p : P, S p) ≤
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
  apply encoded_rectangle_packing P hP S b (2 ^ b / f.natDegree) e A B (2 * T) l
    (by omega) hpT hlarge _ (by positivity)
  intro z hz
  have htail := encoded_rectangle_irreducible_line_tail f hf hd P hP hne S hcard hroot
    b (2 ^ b / f.natDegree) e A B T hT hpT η hη hgap z hz
  have hA : ((encodedBitEvent b e (rectangleRootWitnessEvent P S z A B)).card : ℝ) /
      2 ^ Fintype.card (P × Fin b) ≤ Real.exp (-(η ^ 2 / 2) * (2 * q * l)) := by
    simpa only [Fintype.card_fun, Fintype.card_bool, hcount, Nat.cast_mul,
      Nat.cast_pow, Nat.cast_ofNat, neg_mul, neg_div, div_mul_eq_mul_div] using htail
  exact scheduled_harper_expansion (b * q) q l hm hl hdim (η ^ 2 / 2)
    hschedule _ hA

/-- A deliberately coarse block width makes the all-line estimate decay at
a definite rate after the exact-balancing penalty. The prime and rectangle
conditions remain explicit; they are not consequences of Harper alone. -/
theorem harper_rectangle_exp_tail (f : Polynomial ℤ) (hf : Irreducible f)
    (hd : 2 ≤ f.natDegree)
    (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    (S : (p : ℕ) → Finset (ZMod p)) (hcard : ∀ p ∈ P, (S p).card = f.natDegree)
    (hroot : ∀ p ∈ P, ∀ ρ ∈ S p, f.eval₂ (Int.castRingHom (ZMod p)) ρ = 0)
    (q l : ℕ) (hq : 0 < q) (hl : 1 ≤ l) (hcount : P.card = 2 * q * l)
    (A B T : ℕ) (hT : 2 ≤ T) (hpT : ∀ p ∈ P, p ≤ 2 * T) (η : ℝ) (hη : 0 ≤ η)
    (hschedule : 3 ≤ (η ^ 2 / 2) * q)
    (hgap : Real.log ((max A B : ℕ) : ℝ) +
      Real.log (coefficientBound f f.natDegree : ℝ) / f.natDegree +
      η * P.card * Real.log (T : ℝ) ≤ ∑ p ∈ P, Real.log (p : ℝ))
    (hlarge : (2 * A * B) * (2 * T) ^ (2 * l) < ∏ p ∈ P, p) :
    let b := 16 * f.natDegree * q ^ 2 + 4
    ((rectangleWitnessEvent P S A B).card : ℝ) / Fintype.card (∀ p : P, S p) ≤
      Real.exp (-(l : ℝ) / (4 * (b * q : ℕ))) := by
  dsimp
  let b := 16 * f.natDegree * q ^ 2 + 4
  obtain ⟨hm, hb, hQ⟩ := explicit_balanced_growth_block f.natDegree q hq
  change 2 ≤ b * q at hm
  change 2 * f.natDegree ≤ 2 ^ b at hb
  change 16 * f.natDegree * (b * q) * q ≤ 2 ^ b at hQ
  have hbound := harper_rectangle_bound f hf hd P hP S hcard hroot b q l hb hm hl
    hcount A B T hT hpT η hη hschedule hgap hlarge
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

/-- A convenient dyadic form of the rectangle lemma. Explicit size and area
budgets imply both the logarithmic tail gap and the prime-product separation;
no expansion, line-cover or packing assumption is left in the statement. -/
theorem harper_rectangle_exp_tail_of_dyadic_bounds (f : Polynomial ℤ) (hf : Irreducible f)
    (hd : 2 ≤ f.natDegree)
    (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    (S : (p : ℕ) → Finset (ZMod p)) (hcard : ∀ p ∈ P, (S p).card = f.natDegree)
    (hroot : ∀ p ∈ P, ∀ ρ ∈ S p, f.eval₂ (Int.castRingHom (ZMod p)) ρ = 0)
    (q l : ℕ) (hq : 2 ≤ q) (hl : 1 ≤ l) (hcount : P.card = 2 * q * l)
    (A B T : ℕ) (hT : 2 ≤ T) (hlo : ∀ p ∈ P, T ≤ p) (hhi : ∀ p ∈ P, p ≤ 2 * T)
    (η : ℝ) (hη : 0 ≤ η) (hschedule : 3 ≤ (η ^ 2 / 2) * q)
    (hsize : Real.log ((max A B : ℕ) : ℝ) +
      Real.log (coefficientBound f f.natDegree : ℝ) / f.natDegree ≤
      (1 - η) * P.card * Real.log (T : ℝ))
    (harea : 2 * A * B < T ^ ((2 * q - 4) * l)) :
    let b := 16 * f.natDegree * q ^ 2 + 4
    ((rectangleWitnessEvent P S A B).card : ℝ) / Fintype.card (∀ p : P, S p) ≤
      Real.exp (-(l : ℝ) / (4 * (b * q : ℕ))) :=
  harper_rectangle_exp_tail f hf hd P hP S hcard hroot q l (by omega) hl hcount
    A B T hT hhi η hη hschedule
    (rectangle_log_gap_of_dyadic_lower P T (by omega) hlo _ η hsize)
    (rectangle_separation_of_dyadic_bounds P T q l A B hT hq hcount hlo harea)

/-- Concrete local rectangle theorem: q=12 and eta=3/4. The one displayed
radius/coefficient budget also implies arithmetic separation, so no separate
area budget, expansion premise or finite-line input is required. -/
theorem harper_rectangle_exp_tail_concrete (f : Polynomial ℤ) (hf : Irreducible f)
    (hd : 2 ≤ f.natDegree)
    (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    (S : (p : ℕ) → Finset (ZMod p)) (hcard : ∀ p ∈ P, (S p).card = f.natDegree)
    (hroot : ∀ p ∈ P, ∀ ρ ∈ S p, f.eval₂ (Int.castRingHom (ZMod p)) ρ = 0)
    (l : ℕ) (hl : 1 ≤ l) (hcount : P.card = 24 * l)
    (A B T : ℕ) (hT : 2 ≤ T) (hlo : ∀ p ∈ P, T ≤ p) (hhi : ∀ p ∈ P, p ≤ 2 * T)
    (hsize : Real.log ((max A B : ℕ) : ℝ) +
      Real.log (coefficientBound f f.natDegree : ℝ) / f.natDegree ≤
      6 * l * Real.log (T : ℝ)) :
    let b := 2304 * f.natDegree + 4
    ((rectangleWitnessEvent P S A B).card : ℝ) / Fintype.card (∀ p : P, S p) ≤
      Real.exp (-(l : ℝ) / (48 * (b : ℝ))) := by
  have hC : 0 ≤ Real.log (coefficientBound f f.natDegree : ℝ) / f.natDegree := by
    apply div_nonneg _ (Nat.cast_nonneg _)
    apply Real.log_nonneg
    exact_mod_cast (show 1 ≤ coefficientBound f f.natDegree by unfold coefficientBound; omega)
  have harea := rectangle_area_of_radius_log A B T l hT hl
    ((le_add_of_nonneg_right hC).trans hsize)
  have hsize' : Real.log ((max A B : ℕ) : ℝ) +
      Real.log (coefficientBound f f.natDegree : ℝ) / f.natDegree ≤
      (1 - (3 / 4 : ℝ)) * P.card * Real.log (T : ℝ) := by
    rw [hcount]
    convert hsize using 1
    push_cast
    ring
  have htail := harper_rectangle_exp_tail_of_dyadic_bounds f hf hd P hP S hcard hroot
    12 l (by norm_num) hl (by simpa only [show (2 : ℕ) * 12 = 24 by norm_num] using hcount)
    A B T hT hlo hhi (3 / 4) (by norm_num) (by norm_num) hsize' (by simpa using harea)
  dsimp only at htail ⊢
  have hb : 16 * f.natDegree * 12 ^ 2 + 4 = 2304 * f.natDegree + 4 := by ring
  rw [hb] at htail
  have hden : (4 : ℝ) * ((2304 * f.natDegree + 4) * 12 : ℕ) =
      48 * ((2304 * f.natDegree + 4 : ℕ) : ℝ) := by push_cast; ring
  rwa [hden] at htail

end BinaryFormMoat.HarperIntegration
