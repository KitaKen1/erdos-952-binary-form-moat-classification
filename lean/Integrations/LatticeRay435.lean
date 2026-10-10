import Integrations.LatticeSimplePrefix435
import Mathlib.Order.KonigLemma

noncomputable section
open scoped Classical
namespace BinaryFormMoat.FiniteSieveIntegration
open EntropyIntegration

/-- An infinite component supplies every finite simple-prefix length:
choose a point outside the actual finite displacement box and erase loops. -/
theorem latticeSimplePrefix_nonempty_of_infinite_component
    (A : Set Point) (D : ℕ) (x : Point) (hx : x ∈ A)
    (hInf : (latticeComponent A D x).Infinite) (n : ℕ) :
    Nonempty (LatticeSimplePrefix A D x n) := by
  obtain ⟨y, hy, houtside⟩ := hInf.exists_notMem_finset
    ((displacementBox (D * n)).image (fun v => x + v))
  obtain ⟨p⟩ := latticeReach_graph_reachable hx hy.1 hy.2
  let q := p.toPath
  have hlen : n ≤ q.val.length := by
    by_contra h
    have hd := (latticeGraph_walk_dist_le q.val).trans
      (Nat.mul_le_mul_left D (by omega : q.val.length ≤ n))
    apply houtside
    exact Finset.mem_image.mpr ⟨y - x, displacement_mem_of_latticeDist_le hd, by abel⟩
  refine ⟨⟨(fun i => (q.val.getVert i.val).val), ?_, ?_, ?_, ?_⟩⟩
  · simp
  · intro i; exact (q.val.getVert i.val).property
  · intro i j hij
    apply Fin.ext
    exact q.property.getVert_injOn
      (show i.val ≤ q.val.length from (Nat.le_of_lt_succ i.isLt).trans hlen)
      (show j.val ≤ q.val.length from (Nat.le_of_lt_succ j.isLt).trans hlen) (Subtype.ext hij)
  · intro i
    exact (q.val.adj_getVert_succ (i := i.val) (lt_of_lt_of_le i.isLt hlen)).2

/-- The inverse-system formulation of mathlib's Konig lemma constructs a
genuine infinite self-avoiding walk. Every finite prefix alphabet is finite
by its derived displacement bound, not by an assumed finite component. -/
theorem latticeRay_of_infinite_component (A : Set Point) (D : ℕ) (x : Point)
    (hx : x ∈ A) (hInf : (latticeComponent A D x).Infinite) :
    ∃ z : ℕ → Point, z 0 = x ∧ Function.Injective z ∧
      (∀ n, z n ∈ A) ∧ (∀ n, latticeDist (z n) (z (n + 1)) ≤ D) := by
  let : ∀ n, Nonempty (LatticeSimplePrefix A D x n) :=
    fun n => latticeSimplePrefix_nonempty_of_infinite_component A D x hx hInf n
  obtain ⟨p, hp⟩ := exists_seq_forall_proj_of_forall_finite
    (α := fun n => LatticeSimplePrefix A D x n)
    (fun {_ _} h q => latticePrefixRestrict h q)
    (fun {_} q => latticePrefixRestrict_refl q)
    (fun {_ _ _} h h' q => latticePrefixRestrict_trans h h' q)
    (fun _ _ => Set.toFinite _)
  let z := fun n => (p n).pos ⟨n, by omega⟩
  have hlookup : ∀ n N (h : n ≤ N), z n = (p N).pos ⟨n, by omega⟩ := by
    intro n N h
    exact (congrArg (fun q : LatticeSimplePrefix A D x n => q.pos ⟨n, by omega⟩) (hp h)).symm
  refine ⟨z, (p 0).start, ?_, (fun n => (p n).mem _), ?_⟩
  · intro n m hnm
    rw [hlookup n (n + m) (by omega), hlookup m (n + m) (by omega)] at hnm
    exact congrArg Fin.val ((p (n + m)).injective hnm)
  · intro n
    rw [hlookup n (n + 1) (by omega)]
    exact (p (n + 1)).step ⟨n, by omega⟩

/-- No injective infinite bounded-step walk implies actual finite components.
Starts outside A are handled by reachability and are not silently discarded. -/
theorem finiteComponents_of_no_injective_lattice_walk (A : Set Point) (D : ℕ)
    (hno : ∀ z : ℕ → Point, Function.Injective z → (∀ n, z n ∈ A) →
      (∀ n, latticeDist (z n) (z (n + 1)) ≤ D) → False) : FiniteComponents A D := by
  intro x
  by_contra hInf
  obtain ⟨y, hy⟩ := Set.Infinite.nonempty hInf
  have hx := latticeReach_mem hy.1 (latticeReach_symm hy.2)
  obtain ⟨z, _, hz, hmem, hstep⟩ := latticeRay_of_infinite_component A D x hx hInf
  exact hno z hz hmem hstep

end BinaryFormMoat.FiniteSieveIntegration
#print axioms BinaryFormMoat.FiniteSieveIntegration.latticeSimplePrefix_nonempty_of_infinite_component
#print axioms BinaryFormMoat.FiniteSieveIntegration.latticeRay_of_infinite_component
#print axioms BinaryFormMoat.FiniteSieveIntegration.finiteComponents_of_no_injective_lattice_walk
