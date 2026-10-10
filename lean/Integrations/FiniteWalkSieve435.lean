import Integrations.FiniteSieveExit435
import Mathlib.Combinatorics.SimpleGraph.Paths

namespace BinaryFormMoat.FiniteSieveIntegration

def latticeGraph (A : Set Point) (D : ℕ) : SimpleGraph A where
  Adj x y := x ≠ y ∧ latticeDist x.val y.val ≤ D
  symm := by
    constructor
    intro x y h
    exact ⟨h.1.symm, by rw [latticeDist_symm]; exact h.2⟩
  loopless := by constructor; intro x h; exact h.1 rfl

theorem latticeReach_graph_reachable {A : Set Point} {D : ℕ} {x y : Point}
    (hx : x ∈ A) (hy : y ∈ A) (hxy : latticeReach A D x y) :
    (latticeGraph A D).Reachable ⟨x, hx⟩ ⟨y, hy⟩ := by
  revert hy
  induction hxy with
  | refl => intro hy; exact .rfl
  | @tail u v huv hs ih =>
    intro hv
    have hu := latticeReach_mem hx huv
    have hi := ih hu
    by_cases he : u = v
    · subst v
      exact hi
    · exact hi.trans ⟨.cons ⟨fun he' => he (congrArg Subtype.val he'), hs.2.2⟩ .nil⟩

theorem latticeGraph_walk_dist_le {A : Set Point} {D : ℕ} {x y : A}
    (p : (latticeGraph A D).Walk x y) :
    latticeDist x.val y.val ≤ D * p.length := by
  induction p with
  | nil => simp
  | @cons x y z hxy p ih =>
    have h := (latticeDist_triangle x.val y.val z.val).trans (add_le_add hxy.2 ih)
    simpa only [SimpleGraph.Walk.length_cons, Nat.mul_add, Nat.mul_one, Nat.add_comm] using h

def FiniteWalkBound (A : Set Point) (D N : ℕ) : Prop :=
  ∀ ⦃x y : A⦄, ∀ p : (latticeGraph A D).Walk x y, p.IsPath → p.length ≤ N

/-- Loop erasure is delegated to Mathlib's `toPath`. A single finite-walk
length bound gives a diameter bound without an infinite-path theorem. -/
theorem componentDiameter_of_finiteWalkBound {A : Set Point} {D N : ℕ}
    (hA : FiniteWalkBound A D N) : ComponentDiameter A D (D * N) := by
  classical
  intro x y hx hy hxy
  obtain ⟨p⟩ := latticeReach_graph_reachable hx hy hxy
  let q := p.toPath
  exact (latticeGraph_walk_dist_le q.val).trans (Nat.mul_le_mul_left D (hA q.val q.property))

/-- An alternative target for the entropy proof: all actual samples use only
a finite initial segment. The constructor of this property remains to be proved. -/
def FiniteWalkSieve (F : Form) : Prop :=
  ∀ D (S : Finset ℕ), ∃ P : Finset ℕ,
    (∀ p ∈ P, p.Prime) ∧ Disjoint P S ∧ ∃ N, FiniteWalkBound (avoidPrimes F P) D N

theorem boundedComponentSieve_of_finiteWalkSieve (F : Form) (hF : FiniteWalkSieve F) :
    BoundedComponentSieve F := by
  intro D S
  obtain ⟨P, hP, hPS, N, hN⟩ := hF D S
  exact ⟨P, hP, hPS, D * N, componentDiameter_of_finiteWalkBound hN⟩

theorem uniformMoat_of_finiteWalkSieve (F : Form) (hF : FiniteWalkSieve F) :
    UniformMoat F :=
  uniformMoat_of_boundedComponentSieve F (boundedComponentSieve_of_finiteWalkSieve F hF)

end BinaryFormMoat.FiniteSieveIntegration

#print axioms BinaryFormMoat.FiniteSieveIntegration.latticeGraph
#print axioms BinaryFormMoat.FiniteSieveIntegration.latticeReach_graph_reachable
#print axioms BinaryFormMoat.FiniteSieveIntegration.latticeGraph_walk_dist_le
#print axioms BinaryFormMoat.FiniteSieveIntegration.FiniteWalkBound
#print axioms BinaryFormMoat.FiniteSieveIntegration.componentDiameter_of_finiteWalkBound
#print axioms BinaryFormMoat.FiniteSieveIntegration.FiniteWalkSieve
#print axioms BinaryFormMoat.FiniteSieveIntegration.boundedComponentSieve_of_finiteWalkSieve
#print axioms BinaryFormMoat.FiniteSieveIntegration.uniformMoat_of_finiteWalkSieve
