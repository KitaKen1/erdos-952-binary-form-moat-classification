import Integrations.PrimeBlocks435
import Integrations.WalkDisplacement435

namespace BinaryFormMoat.FiniteSieveIntegration
open EntropyIntegration

theorem latticeDist_le_of_sqDist (R : ℕ) (x y : Point) (h : sqDist x y ≤ (R : ℤ)) :
    latticeDist x y ≤ 2 * (R + 1) := by
  have hx : |x.1 - y.1| ≤ (R + 1 : ℕ) := by
    simpa using linear_step_bound 1 0 R x y h
  have hy : |x.2 - y.2| ≤ (R + 1 : ℕ) := by
    simpa using linear_step_bound 0 1 R x y h
  have hx' : (x.1 - y.1).natAbs ≤ R + 1 := by
    exact_mod_cast (show ((x.1 - y.1).natAbs : ℤ) ≤ (R + 1 : ℕ) by
      simpa only [Int.natCast_natAbs] using hx)
  have hy' : (x.2 - y.2).natAbs ≤ R + 1 := by
    exact_mod_cast (show ((x.2 - y.2).natAbs : ℤ) ≤ (R + 1 : ℕ) by
      simpa only [Int.natCast_natAbs] using hy)
  dsimp [latticeDist]
  omega

theorem graph_reachable_latticeReach (F : Form) (r R : ℕ) (A : Set Point)
    (hsub : ∀ x, Allowed F r x → x ∈ A)
    {x y : {x : Point // Allowed F r x}} (hxy : (graph F r R).Reachable x y) :
    latticeReach A (2 * (R + 1)) x.val y.val := by
  obtain ⟨p⟩ := hxy
  induction p with
  | nil => exact .refl
  | @cons x y z hxy _ ih =>
    exact (latticeReach_single (hsub x.val x.property) (hsub y.val y.property)
      (latticeDist_le_of_sqDist R x.val y.val hxy.2)).trans ih

theorem displacement_mem_of_latticeDist_le {x y : Point} {a : ℕ}
    (h : latticeDist x y ≤ a) : y - x ∈ displacementBox a := by
  have hx : (x.1 - y.1).natAbs ≤ a := by dsimp [latticeDist] at h; omega
  have hy : (x.2 - y.2).natAbs ≤ a := by dsimp [latticeDist] at h; omega
  apply (mem_displacementBox a (y - x)).mpr
  constructor
  · have hc : |x.1 - y.1| ≤ (a : ℤ) := by
      simpa only [Int.natCast_natAbs] using (show ((x.1 - y.1).natAbs : ℤ) ≤ a by exact_mod_cast hx)
    simpa only [Prod.fst_sub, abs_sub_comm] using hc
  · have hc : |x.2 - y.2| ≤ (a : ℤ) := by
      simpa only [Int.natCast_natAbs] using (show ((x.2 - y.2).natAbs : ℤ) ≤ a by exact_mod_cast hy)
    simpa only [Prod.snd_sub, abs_sub_comm] using hc

/-- Any bounded-component superset bounds the original graph, uniformly in
the starting point. No periodicity of the original omega-budget set is assumed. -/
theorem component_bound_of_latticeDiameter (F : Form) (r R a : ℕ) (A : Set Point)
    (hsub : ∀ x, Allowed F r x → x ∈ A)
    (hA : ComponentDiameter A (2 * (R + 1)) a)
    (z : {x : Point // Allowed F r x}) :
    Set.encard {w | (graph F r R).Reachable z w} ≤ ((2 * a + 1) ^ 2 : ℕ) := by
  have hcard := Set.encard_le_encard_of_injOn
    (s := {w | (graph F r R).Reachable z w})
    (f := fun w : {x : Point // Allowed F r x} => w.val - z.val)
    (t := (displacementBox a : Set Point))
    (fun w hw => displacement_mem_of_latticeDist_le
      (hA (hsub z.val z.property) (hsub w.val w.property)
        (graph_reachable_latticeReach F r R A hsub hw)))
    (fun x _ y _ hxy => Subtype.ext (sub_left_inj.mp hxy))
  rw [Set.encard_coe_eq_coe_finsetCard, displacementBox_card] at hcard
  exact hcard

theorem uniformMoat_of_boundedComponentSieve (F : Form) (hF : BoundedComponentSieve F) :
    UniformMoat F := by
  intro R r
  obtain ⟨P, hP, _, hdis, a, hA⟩ :=
    exists_disjoint_bounded_blocks F hF (2 * (R + 1)) (r + 1) ∅
  refine ⟨(2 * a + 1) ^ 2, ?_⟩
  exact component_bound_of_latticeDiameter F r R a (blockAvoid F P)
    (fun z hz => allowed_mem_blockAvoid F r P hP hdis z hz) hA

/-- The complete arbitrary-budget exit; the entropy proof still owes hF. -/
theorem uniformMoat_of_finiteComponentSieve (F : Form) (hF : FiniteComponentSieve F) :
    UniformMoat F :=
  uniformMoat_of_boundedComponentSieve F (boundedComponentSieve_of_finiteComponentSieve F hF)

end BinaryFormMoat.FiniteSieveIntegration

#print axioms BinaryFormMoat.FiniteSieveIntegration.latticeDist_le_of_sqDist
#print axioms BinaryFormMoat.FiniteSieveIntegration.graph_reachable_latticeReach
#print axioms BinaryFormMoat.FiniteSieveIntegration.displacement_mem_of_latticeDist_le
#print axioms BinaryFormMoat.FiniteSieveIntegration.component_bound_of_latticeDiameter
#print axioms BinaryFormMoat.FiniteSieveIntegration.uniformMoat_of_boundedComponentSieve
#print axioms BinaryFormMoat.FiniteSieveIntegration.uniformMoat_of_finiteComponentSieve
