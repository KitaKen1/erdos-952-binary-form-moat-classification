import Integrations.FiniteWalkSieve435

noncomputable section
open scoped Classical
namespace BinaryFormMoat.FiniteSieveIntegration
open EntropyIntegration

/-- A genuine length-n simple lattice-walk prefix from one fixed start. -/
structure LatticeSimplePrefix (A : Set Point) (D : ℕ) (x : Point) (n : ℕ) where
  pos : Fin (n + 1) → Point
  start : pos 0 = x
  mem : ∀ i, pos i ∈ A
  injective : Function.Injective pos
  step : ∀ i : Fin n, latticeDist (pos i.castSucc) (pos i.succ) ≤ D

theorem LatticeSimplePrefix.ext {A : Set Point} {D : ℕ} {x : Point} {n : ℕ}
    (p q : LatticeSimplePrefix A D x n) (h : p.pos = q.pos) : p = q := by
  cases p
  cases q
  cases h
  rfl

theorem LatticeSimplePrefix.distance {A : Set Point} {D : ℕ} {x : Point} {n : ℕ}
    (p : LatticeSimplePrefix A D x n) (i : Fin (n + 1)) :
    latticeDist x (p.pos i) ≤ D * i.val := by
  have h : ∀ k (hk : k < n + 1), latticeDist x (p.pos ⟨k, hk⟩) ≤ D * k := by
    intro k
    induction k with
    | zero =>
      intro hk
      change latticeDist x (p.pos 0) ≤ 0
      rw [p.start, latticeDist_self]
    | succ k ih =>
      intro hk
      have hs := p.step ⟨k, by omega⟩
      have hb := (latticeDist_triangle x (p.pos ⟨k, by omega⟩)
        (p.pos ⟨k + 1, hk⟩)).trans (add_le_add (ih (by omega)) hs)
      simpa only [Nat.mul_add, Nat.mul_one] using hb
  exact h i.val i.isLt

/-- Finite displacement boxes, rather than a global finite vertex set,
give finiteness of every actual simple-prefix alphabet. -/
instance latticeSimplePrefix_finite (A : Set Point) (D : ℕ) (x : Point) (n : ℕ) :
    Finite (LatticeSimplePrefix A D x n) := by
  let encode : LatticeSimplePrefix A D x n → (Fin (n + 1) → BoundedDisplacement (D * n)) :=
    fun p i => ⟨p.pos i - x, displacement_mem_of_latticeDist_le
      ((p.distance i).trans (Nat.mul_le_mul_left D (by have := i.isLt; omega)))⟩
  apply Finite.of_injective encode
  intro p q h
  apply LatticeSimplePrefix.ext
  funext i
  exact sub_left_inj.mp (congrArg Subtype.val (congrFun h i))

/-- Restriction preserves actual vertices, membership, simple-path property
and the original bounded steps. -/
def latticePrefixRestrict {A : Set Point} {D : ℕ} {x : Point} {i j : ℕ}
    (hij : i ≤ j) (p : LatticeSimplePrefix A D x j) : LatticeSimplePrefix A D x i where
  pos k := p.pos ⟨k.val, by have := k.isLt; omega⟩
  start := p.start
  mem k := p.mem _
  injective := by
    intro a b hab
    exact Fin.ext (congrArg (fun k : Fin (j + 1) => k.val) (p.injective hab))
  step k := p.step ⟨k.val, by have := k.isLt; omega⟩

theorem latticePrefixRestrict_refl {A : Set Point} {D : ℕ} {x : Point} {i : ℕ}
    (p : LatticeSimplePrefix A D x i) : latticePrefixRestrict (le_refl i) p = p := by
  apply LatticeSimplePrefix.ext
  rfl

theorem latticePrefixRestrict_trans {A : Set Point} {D : ℕ} {x : Point} {i j k : ℕ}
    (hij : i ≤ j) (hjk : j ≤ k) (p : LatticeSimplePrefix A D x k) :
    latticePrefixRestrict hij (latticePrefixRestrict hjk p) =
      latticePrefixRestrict (hij.trans hjk) p := by
  apply LatticeSimplePrefix.ext
  rfl

end BinaryFormMoat.FiniteSieveIntegration
#print axioms BinaryFormMoat.FiniteSieveIntegration.LatticeSimplePrefix
#print axioms BinaryFormMoat.FiniteSieveIntegration.LatticeSimplePrefix.ext
#print axioms BinaryFormMoat.FiniteSieveIntegration.LatticeSimplePrefix.distance
#print axioms BinaryFormMoat.FiniteSieveIntegration.latticeSimplePrefix_finite
#print axioms BinaryFormMoat.FiniteSieveIntegration.latticePrefixRestrict
#print axioms BinaryFormMoat.FiniteSieveIntegration.latticePrefixRestrict_refl
#print axioms BinaryFormMoat.FiniteSieveIntegration.latticePrefixRestrict_trans
