import Integrations.FiniteUnion435
import Moat.Sieve

namespace BinaryFormMoat.FiniteSieveIntegration

def residueHom (Q : ℕ) : Point →+ Residue Q where
  toFun := residue Q
  map_zero' := by simp [residue]
  map_add' := by intro x y; apply Prod.ext <;> simp [residue]

/-- Membership depends only on the residue class. -/
def PeriodicSet (Q : ℕ) (A : Set Point) : Prop :=
  ∀ x y, residue Q x = residue Q y → (x ∈ A ↔ y ∈ A)

def latticeComponent (A : Set Point) (D : ℕ) (x : Point) : Set Point :=
  {y | y ∈ A ∧ latticeReach A D x y}

def FiniteComponents (A : Set Point) (D : ℕ) : Prop :=
  ∀ x, (latticeComponent A D x).Finite

theorem periodicSet_add_kernel {Q : ℕ} {A : Set Point} (hA : PeriodicSet Q A)
    {v : Point} (hv : residueHom Q v = 0) (x : Point) :
    x ∈ A ↔ x + v ∈ A := by
  apply hA x (x + v)
  change residueHom Q x = residueHom Q (x + v)
  simp [hv]

theorem latticeReach_translate {Q D : ℕ} {A : Set Point} (hA : PeriodicSet Q A)
    {v x y : Point} (hv : residueHom Q v = 0) (hxy : latticeReach A D x y) :
    latticeReach A D (x + v) (y + v) := by
  apply Relation.ReflTransGen.lift (fun x : Point => x + v) ?_ x y hxy
  intro a b hab
  exact ⟨(periodicSet_add_kernel hA hv a).mp hab.1,
    (periodicSet_add_kernel hA hv b).mp hab.2.1, by simpa using hab.2.2⟩

theorem latticeOrbit_injective {x v : Point} (hv : v ≠ 0) :
    Function.Injective (fun n : ℕ => x + n • v) := by
  intro n m hnm
  have he : n • v = m • v := add_left_cancel hnm
  have hcoord : v.1 ≠ 0 ∨ v.2 ≠ 0 := by
    by_contra h
    push Not at h
    exact hv (Prod.ext h.1 h.2)
  rcases hcoord with hv1 | hv2
  · have h1 := congrArg Prod.fst he
    change (n : ℤ) * v.1 = (m : ℤ) * v.1 at h1
    exact_mod_cast (mul_right_cancel₀ hv1 h1)
  · have h2 := congrArg Prod.snd he
    change (n : ℤ) * v.2 = (m : ℤ) * v.2 at h2
    exact_mod_cast (mul_right_cancel₀ hv2 h2)

/-- Translation of one same-residue connection makes an unbounded orbit.
This step needs finite components, not a uniform bound supplied in advance. -/
theorem same_residue_eq_of_finite_component {Q D : ℕ} {A : Set Point}
    (hA : PeriodicSet Q A) (hfin : FiniteComponents A D)
    {x y : Point} (hx : x ∈ A) (hxy : latticeReach A D x y)
    (hr : residue Q x = residue Q y) : x = y := by
  by_contra hne
  let v := y - x
  have hv : v ≠ 0 := by
    intro he
    apply hne
    exact (sub_eq_zero.mp he).symm
  have hr0 : residueHom Q v = 0 := by
    change residueHom Q (y - x) = 0
    rw [map_sub]
    change residue Q y - residue Q x = 0
    rw [hr, sub_self]
  have hreach (n : ℕ) : latticeReach A D x (x + n • v) := by
    induction n with
    | zero => simpa using latticeReach_refl A D x
    | succ n ih =>
      have hk : residueHom Q (n • v) = 0 := by rw [map_nsmul, hr0, nsmul_zero]
      have hs := latticeReach_translate hA hk hxy
      have he : y + n • v = x + (n + 1) • v := by
        dsimp [v]
        simp only [add_nsmul, one_nsmul]
        abel
      exact ih.trans (he ▸ hs)
  have hsub : Set.range (fun n : ℕ => x + n • v) ⊆ latticeComponent A D x := by
    rintro z ⟨n, rfl⟩
    exact ⟨latticeReach_mem hx (hreach n), hreach n⟩
  exact (Set.infinite_range_of_injective (latticeOrbit_injective hv))
    ((hfin x).subset hsub)

theorem residue_injOn_component {Q D : ℕ} {A : Set Point}
    (hA : PeriodicSet Q A) (hfin : FiniteComponents A D) (z : Point) :
    Set.InjOn (residue Q) (latticeComponent A D z) := by
  intro x hx y hy hr
  exact same_residue_eq_of_finite_component hA hfin hx.1
    ((latticeReach_symm hx.2).trans hy.2) hr

theorem periodic_component_encard_le {Q D : ℕ} [NeZero Q] {A : Set Point}
    (hA : PeriodicSet Q A) (hfin : FiniteComponents A D) (z : Point) :
    (latticeComponent A D z).encard ≤ (Q * Q : ℕ) := by
  have h := Set.encard_le_encard_of_injOn (t := (Set.univ : Set (Residue Q)))
    (fun _ _ => Set.mem_univ _) (residue_injOn_component hA hfin z)
  simpa [Residue, Fintype.card_prod, ZMod.card] using h

/-- A finite collection of canonical-residue components gives a common
diameter bound. It does not require a separate shortest-path API. -/
theorem periodic_hasBoundedComponents {Q D : ℕ} [NeZero Q] {A : Set Point}
    (hA : PeriodicSet Q A) (hfin : FiniteComponents A D) :
    HasBoundedComponents A D := by
  classical
  let C (u : Residue Q) : Finset Point := (hfin (representative u)).toFinset
  let a := Finset.univ.sup (fun u : Residue Q => (C u).sup (latticeDist (representative u)))
  refine ⟨a, ?_⟩
  intro x y _ hy hxy
  let u := residue Q x
  let v := representative u - x
  have hv : residueHom Q v = 0 := by
    change residueHom Q (representative u - x) = 0
    rw [map_sub]
    change residue Q (representative u) - residue Q x = 0
    simp [residue_representative, u]
  have he : x + v = representative u := by dsimp [v]; abel
  have htr := latticeReach_translate hA hv hxy
  rw [he] at htr
  have hmem : y + v ∈ C u := by
    change y + v ∈ (hfin (representative u)).toFinset
    simpa only [Set.Finite.mem_toFinset] using
      (show y + v ∈ latticeComponent A D (representative u) from
        ⟨(periodicSet_add_kernel hA hv y).mp hy, htr⟩)
  have hl := Finset.le_sup (f := latticeDist (representative u)) hmem
  have hu := Finset.le_sup (f := fun u : Residue Q =>
    (C u).sup (latticeDist (representative u))) (Finset.mem_univ u)
  have hd : latticeDist x y = latticeDist (representative u) (y + v) := by
    rw [← he, latticeDist_add_right]
  rw [hd]
  exact hl.trans hu

end BinaryFormMoat.FiniteSieveIntegration

#print axioms BinaryFormMoat.FiniteSieveIntegration.residueHom
#print axioms BinaryFormMoat.FiniteSieveIntegration.PeriodicSet
#print axioms BinaryFormMoat.FiniteSieveIntegration.latticeComponent
#print axioms BinaryFormMoat.FiniteSieveIntegration.FiniteComponents
#print axioms BinaryFormMoat.FiniteSieveIntegration.periodicSet_add_kernel
#print axioms BinaryFormMoat.FiniteSieveIntegration.latticeReach_translate
#print axioms BinaryFormMoat.FiniteSieveIntegration.latticeOrbit_injective
#print axioms BinaryFormMoat.FiniteSieveIntegration.same_residue_eq_of_finite_component
#print axioms BinaryFormMoat.FiniteSieveIntegration.residue_injOn_component
#print axioms BinaryFormMoat.FiniteSieveIntegration.periodic_component_encard_le
#print axioms BinaryFormMoat.FiniteSieveIntegration.periodic_hasBoundedComponents
