import Mathlib.RingTheory.MvPolynomial.Homogeneous
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.Data.Nat.PrimeFin
import Mathlib.Data.Set.Card
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Binary homogeneous form moat classification: statement prototype

Source: studyreportv1.html, X-BinaryFormMoat, received 2026-10-07,
and the two saved final answers in conversation 6ac60778.

Core definitions and elementary lemmas for the classification project.
Open conjectures live in Moat/Conjectures.lean; this module has no placeholders.
`R` bounds squared Euclidean distance. Quantifying over all natural `R` covers
every finite real step bound, without using square roots in the graph definition.
-/

namespace BinaryFormMoat

abbrev Form := MvPolynomial (Fin 2) ℤ
abbrev Point := ℤ × ℤ

/-- Evaluate the binary form at an integer lattice point. -/
def value (F : Form) (z : Point) : ℤ :=
  MvPolynomial.eval ![z.1, z.2] F

/-- Number of distinct rational prime factors; multiplicities are ignored. -/
def omega (n : ℤ) : ℕ := n.natAbs.primeFactors.card

/-- Zero values are excluded explicitly, even though `omega 0 = 0` in Mathlib. -/
def Allowed (F : Form) (r : ℕ) (z : Point) : Prop :=
  value F z ≠ 0 ∧ omega (value F z) ≤ r

def sqDist (z w : Point) : ℤ := (z.1 - w.1)^2 + (z.2 - w.2)^2

/-- The bounded-step graph on the allowed lattice points. -/
def graph (F : Form) (r R : ℕ) : SimpleGraph {z : Point // Allowed F r z} where
  Adj z w := z ≠ w ∧ sqDist z.val w.val ≤ (R : ℤ)
  symm := by
    constructor
    intro z w h
    refine ⟨h.1.symm, ?_⟩
    have heq : sqDist w.val z.val = sqDist z.val w.val := by
      unfold sqDist
      ring
    simpa only [heq] using h.2
  loopless := by
    constructor
    intro z h
    exact h.1 rfl

/-- The component bound may depend on F, R and r, but not on its initial vertex.
Extended cardinality keeps infinite components from being assigned cardinality zero. -/
def UniformMoat (F : Form) : Prop :=
  ∀ (R r : ℕ), ∃ B : ℕ, ∀ z : {z : Point // Allowed F r z},
    Set.encard {w | (graph F r R).Reachable z w} ≤ (B : ℕ∞)

/-- The exceptional forms c(aX+bY)^m, with nonzero c and linear form. -/
def IsLinearPower (F : Form) : Prop :=
  ∃ (c a b : ℤ) (m : ℕ), c ≠ 0 ∧ (a ≠ 0 ∨ b ≠ 0) ∧ 0 < m ∧
    F = MvPolynomial.C c *
      (MvPolynomial.C a * MvPolynomial.X (0 : Fin 2) +
       MvPolynomial.C b * MvPolynomial.X (1 : Fin 2)) ^ m

/-- The value zero must not accidentally enter the graph. -/
theorem zero_value_excluded (F : Form) (r : ℕ) (z : Point)
    (hz : value F z = 0) : ¬ Allowed F r z := by
  intro h
  exact h.1 hz

/-- Units use no prime-factor budget. -/
theorem omega_one : omega 1 = 0 := by
  norm_num [omega]

/-- Prime powers use one distinct prime, not their exponent. -/
theorem omega_prime_power (p k : ℕ) (hp : p.Prime) (hk : k ≠ 0) :
    omega ((p : ℤ)^k) = 1 := by
  simp [omega, Int.natAbs_pow, Nat.primeFactors_prime_pow hk hp]

/-- The exceptional example X² admits every point (1,t) at budget zero. -/
theorem x_sq_line_allowed (t : ℤ) :
    Allowed ((MvPolynomial.X (0 : Fin 2) : Form)^2) 0 (1, t) := by
  norm_num [Allowed, value, omega]

/-- Consecutive points on the exceptional line have squared distance one. -/
theorem x_sq_line_step (t : ℤ) : sqDist (1, t) (1, t + 1) = 1 := by
  unfold sqDist
  ring

end BinaryFormMoat
