import Moat.Barriers
import Moat.Certificate
import Moat.Reduction
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.LinearCombination

namespace BinaryFormMoat

/-- Two injective coordinates, each with a bounded prime budget and bounded increments,
trap every component between periodic CRT walls. -/
theorem uniformMoat_of_prime_budget_coordinates (F : Form) (f g : Point → ℤ)
    (hinj : Function.Injective (fun z => (f z, g z)))
    (hallowed : ∀ r z, Allowed F r z →
      (f z ≠ 0 ∧ omega (f z) ≤ r) ∧ (g z ≠ 0 ∧ omega (g z) ≤ r))
    (hstep : ∀ R : ℕ, ∃ W : ℕ, ∀ z w, sqDist z w ≤ (R : ℤ) →
      |f z - f w| ≤ W ∧ |g z - g w| ≤ W) : UniformMoat F := by
  intro R r
  obtain ⟨W, hW⟩ := hstep R
  obtain ⟨a, Q, hQ, hwall⟩ := exists_prime_budget_wall r W
  let : NeZero Q := ⟨ne_of_gt hQ⟩
  let V := {z : Point // Allowed F r z}
  let label : V → ZMod Q × ZMod Q := fun z =>
    ((f z.val - a : ℤ), (g z.val - a : ℤ))
  let cell : V → ℤ × ℤ := fun z => ((f z.val - a) / Q, (g z.val - a) / Q)
  refine ⟨Fintype.card (ZMod Q × ZMod Q), fun z => ?_⟩
  apply component_bound_of_label (graph F r R) label cell _ _ z
  · intro x y hxy
    obtain ⟨hfx, hgx⟩ := hallowed r x.val x.property
    obtain ⟨hfy, hgy⟩ := hallowed r y.val y.property
    obtain ⟨hfstep, hgstep⟩ := hW x.val y.val hxy.2
    apply Prod.ext
    · apply wall_cell_eq (Q : ℤ) W _ _ (by exact_mod_cast hQ)
        (hwall _ hfx.1 hfx.2) (hwall _ hfy.1 hfy.2)
      · linarith [(abs_le.mp hfstep).2]
      · linarith [(abs_le.mp hfstep).1]
    · apply wall_cell_eq (Q : ℤ) W _ _ (by exact_mod_cast hQ)
        (hwall _ hgx.1 hgx.2) (hwall _ hgy.1 hgy.2)
      · linarith [(abs_le.mp hgstep).2]
      · linarith [(abs_le.mp hgstep).1]
  · intro x y hcell hlabel
    have recover (s t : ℤ) (hc : s / Q = t / Q)
        (hl : (s : ZMod Q) = (t : ZMod Q)) : s = t := by
      have hm := (ZMod.intCast_eq_intCast_iff' s t Q).mp hl
      have hs := Int.emod_add_mul_ediv s (Q : ℤ)
      have ht := Int.emod_add_mul_ediv t (Q : ℤ)
      rw [hc, hm] at hs
      omega
    apply Subtype.ext
    apply hinj
    apply Prod.ext
    · have he := recover (f x.val - a) (f y.val - a)
        (congrArg Prod.fst hcell) (congrArg Prod.fst hlabel)
      linarith
    · have he := recover (g x.val - a) (g y.val - a)
        (congrArg Prod.snd hcell) (congrArg Prod.snd hlabel)
      linarith

/-- A homogeneous linear polynomial. -/
noncomputable def linearForm (a b : ℤ) : Form :=
  MvPolynomial.C a * MvPolynomial.X (0 : Fin 2) +
    MvPolynomial.C b * MvPolynomial.X (1 : Fin 2)

@[simp] theorem value_linearForm (a b : ℤ) (z : Point) :
    value (linearForm a b) z = a * z.1 + b * z.2 := by
  simp [value, linearForm]

/-- Independent linear forms jointly separate lattice points. -/
theorem linear_coordinates_injective (a b c d : ℤ) (hdet : a * d - b * c ≠ 0) :
    Function.Injective (fun z : Point => (a * z.1 + b * z.2, c * z.1 + d * z.2)) := by
  intro z w h
  have h₁ := congrArg Prod.fst h
  have h₂ := congrArg Prod.snd h
  dsimp at h₁ h₂
  have hx : (a * d - b * c) * (z.1 - w.1) = 0 := by
    linear_combination d * h₁ - b * h₂
  have hy : (a * d - b * c) * (z.2 - w.2) = 0 := by
    linear_combination a * h₂ - c * h₁
  exact Prod.ext (sub_eq_zero.mp ((mul_eq_zero.mp hx).resolve_left hdet))
    (sub_eq_zero.mp ((mul_eq_zero.mp hy).resolve_left hdet))

/-- A deliberately loose integral Lipschitz bound avoids square-root estimates. -/
theorem linear_step_bound (a b : ℤ) (R : ℕ) (z w : Point)
    (h : sqDist z w ≤ (R : ℤ)) :
    |(a * z.1 + b * z.2) - (a * w.1 + b * w.2)| ≤
      ((a.natAbs + b.natAbs) * (R + 1) : ℕ) := by
  have hR : (0 : ℤ) ≤ R := Int.natCast_nonneg R
  have hx : |z.1 - w.1| ≤ (R : ℤ) + 1 := by
    dsimp [sqDist] at h
    nlinarith [sq_nonneg (z.2 - w.2), sq_abs (z.1 - w.1),
      sq_nonneg (|z.1 - w.1| - 1)]
  have hy : |z.2 - w.2| ≤ (R : ℤ) + 1 := by
    dsimp [sqDist] at h
    nlinarith [sq_nonneg (z.1 - w.1), sq_abs (z.2 - w.2),
      sq_nonneg (|z.2 - w.2| - 1)]
  calc
    _ = |a * (z.1 - w.1) + b * (z.2 - w.2)| := by congr 1; ring
    _ ≤ |a * (z.1 - w.1)| + |b * (z.2 - w.2)| := abs_add_le _ _
    _ = |a| * |z.1 - w.1| + |b| * |z.2 - w.2| := by rw [abs_mul, abs_mul]
    _ ≤ |a| * ((R : ℤ) + 1) + |b| * ((R : ℤ) + 1) :=
      add_le_add (mul_le_mul_of_nonneg_left hx (abs_nonneg a))
        (mul_le_mul_of_nonneg_left hy (abs_nonneg b))
    _ = _ := by push_cast; ring

/-- The complete sufficiency branch for any polynomial with two independent linear divisors.
No homogeneity or restriction on the prime budget or step bound is required. -/
theorem uniformMoat_of_independent_linear_divisors (F : Form) (a b c d : ℤ)
    (hdet : a * d - b * c ≠ 0)
    (h₁ : linearForm a b ∣ F) (h₂ : linearForm c d ∣ F) : UniformMoat F := by
  apply uniformMoat_of_prime_budget_coordinates F
    (fun z => a * z.1 + b * z.2) (fun z => c * z.1 + d * z.2)
    (linear_coordinates_injective a b c d hdet)
  · intro r z hz
    constructor
    · simpa only [Allowed, value_linearForm] using allowed_of_dvd h₁ r z hz
    · simpa only [Allowed, value_linearForm] using allowed_of_dvd h₂ r z hz
  · intro R
    let W₁ := (a.natAbs + b.natAbs) * (R + 1)
    let W₂ := (c.natAbs + d.natAbs) * (R + 1)
    refine ⟨max W₁ W₂, fun z w h => ?_⟩
    constructor
    · exact (linear_step_bound a b R z w h).trans (by exact_mod_cast Nat.le_max_left W₁ W₂)
    · exact (linear_step_bound c d R z w h).trans (by exact_mod_cast Nat.le_max_right W₁ W₂)

/-- In particular, XY has uniformly bounded components at every finite budget and step size. -/
theorem uniformMoat_X_mul_Y :
    UniformMoat ((MvPolynomial.X (0 : Fin 2) : Form) * MvPolynomial.X (1 : Fin 2)) := by
  apply uniformMoat_of_independent_linear_divisors _ 1 0 0 1 (by norm_num)
  · simp [linearForm]
  · simp [linearForm]

end BinaryFormMoat
