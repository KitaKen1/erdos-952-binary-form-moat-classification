import Moat.PeriodicCertificate
import Mathlib.Logic.Relation

/-! The finite-union exit of the paper, using integer Manhattan distance.
This is equivalent for an all-step-bounds moat statement and avoids square roots.
The reflexive reachability relation is only used with a start in the allowed set. -/

namespace BinaryFormMoat.FiniteSieveIntegration

def latticeDist (x y : Point) : ℕ :=
  (x.1 - y.1).natAbs + (x.2 - y.2).natAbs

@[simp] theorem latticeDist_self (x : Point) : latticeDist x x = 0 := by
  simp [latticeDist]

theorem latticeDist_symm (x y : Point) : latticeDist x y = latticeDist y x := by
  have h (a b : ℤ) : (a - b).natAbs = (b - a).natAbs := by
    rw [← Int.natAbs_neg (a - b)]
    congr 1
    ring
  simp only [latticeDist, h]

theorem latticeDist_triangle (x y z : Point) :
    latticeDist x z ≤ latticeDist x y + latticeDist y z := by
  have hx := Int.natAbs_add_le (x.1 - y.1) (y.1 - z.1)
  have hy := Int.natAbs_add_le (x.2 - y.2) (y.2 - z.2)
  have ex : x.1 - y.1 + (y.1 - z.1) = x.1 - z.1 := by ring
  have ey : x.2 - y.2 + (y.2 - z.2) = x.2 - z.2 := by ring
  rw [ex] at hx
  rw [ey] at hy
  dsimp [latticeDist]
  omega

@[simp] theorem latticeDist_add_right (x y v : Point) :
    latticeDist (x + v) (y + v) = latticeDist x y := by
  simp [latticeDist, add_sub_add_right_eq_sub]

def latticeStep (A : Set Point) (D : ℕ) (x y : Point) : Prop :=
  x ∈ A ∧ y ∈ A ∧ latticeDist x y ≤ D

def latticeReach (A : Set Point) (D : ℕ) (x y : Point) : Prop :=
  Relation.ReflTransGen (latticeStep A D) x y

theorem latticeReach_refl (A : Set Point) (D : ℕ) (x : Point) :
    latticeReach A D x x := .refl

theorem latticeReach_single {A : Set Point} {D : ℕ} {x y : Point}
    (hx : x ∈ A) (hy : y ∈ A) (hxy : latticeDist x y ≤ D) :
    latticeReach A D x y := .single ⟨hx, hy, hxy⟩

theorem latticeReach_trans {A : Set Point} {D : ℕ} {x y z : Point}
    (hxy : latticeReach A D x y) (hyz : latticeReach A D y z) :
    latticeReach A D x z := hxy.trans hyz

theorem latticeReach_mem {A : Set Point} {D : ℕ} {x y : Point}
    (hx : x ∈ A) (h : latticeReach A D x y) : y ∈ A := by
  induction h with
  | refl => exact hx
  | tail _ hs _ => exact hs.2.1

theorem latticeReach_symm {A : Set Point} {D : ℕ} {x y : Point}
    (h : latticeReach A D x y) : latticeReach A D y x := by
  induction h with
  | refl => exact .refl
  | @tail y z _ hs ih =>
    exact (latticeReach_single hs.2.1 hs.1 (by rw [latticeDist_symm]; exact hs.2.2)).trans ih

theorem latticeReach_mono {A B : Set Point} {D E : ℕ} {x y : Point}
    (hAB : A ⊆ B) (hDE : D ≤ E) (h : latticeReach A D x y) :
    latticeReach B E x y := by
  apply Relation.ReflTransGen.mono ?_ x y h
  intro u v huv
  exact ⟨hAB huv.1, hAB huv.2.1, huv.2.2.trans hDE⟩

def ComponentDiameter (A : Set Point) (D a : ℕ) : Prop :=
  ∀ ⦃x y⦄, x ∈ A → y ∈ A → latticeReach A D x y → latticeDist x y ≤ a

def HasBoundedComponents (A : Set Point) (D : ℕ) : Prop :=
  ∃ a, ComponentDiameter A D a

/-- A tail from the last visit to B, followed only by an A-component. -/
def componentTail (A : Set Point) (D : ℕ) (b y : Point) : Prop :=
  b = y ∨ ∃ u, u ∈ A ∧ latticeDist b u ≤ D ∧ latticeReach A D u y

theorem componentTail_dist {A : Set Point} {D a : ℕ}
    (hA : ComponentDiameter A D a) {b y : Point} (h : componentTail A D b y) :
    latticeDist b y ≤ a + D := by
  rcases h with rfl | ⟨u, hu, hbu, huy⟩
  · simp
  · have hy := latticeReach_mem hu huy
    have hd := hA hu hy huy
    have ht := latticeDist_triangle b u y
    omega

theorem componentTail_extend {A : Set Point} {D : ℕ} {b x y : Point}
    (h : componentTail A D b x) (hy : y ∈ A) (hxy : latticeDist x y ≤ D) :
    componentTail A D b y := by
  rcases h with rfl | ⟨u, hu, hbu, hux⟩
  · exact Or.inr ⟨y, hy, hxy, .refl⟩
  · exact Or.inr ⟨u, hu, hbu,
      hux.trans (latticeReach_single (latticeReach_mem hu hux) hy hxy)⟩

/-- Compression of an arbitrary union walk to successive B visits. -/
theorem union_reach_decomposition {A B : Set Point} {D a : ℕ}
    (hA : ComponentDiameter A D a) {x y : Point} (hx : x ∈ A ∪ B)
    (hxy : latticeReach (A ∪ B) D x y) :
    (x ∈ A ∧ latticeReach A D x y) ∨
      ∃ b c, b ∈ B ∧ c ∈ B ∧ latticeDist x b ≤ a + D ∧
        latticeReach B (a + 2 * D) b c ∧ componentTail A D c y := by
  induction hxy with
  | refl =>
    rcases hx with hx | hx
    · exact Or.inl ⟨hx, .refl⟩
    · exact Or.inr ⟨x, x, hx, hx, by simp, .refl, Or.inl rfl⟩
  | @tail u v _ huv ih =>
    have hstep := huv.2.2
    by_cases hvB : v ∈ B
    · rcases ih with ⟨hxA, hxu⟩ | ⟨b, c, hb, hc, hxb, hbc, hcu⟩
      · have huA := latticeReach_mem hxA hxu
        have hd := hA hxA huA hxu
        have ht := latticeDist_triangle x u v
        exact Or.inr ⟨v, v, hvB, hvB, by omega, .refl, Or.inl rfl⟩
      · have hd := componentTail_dist hA hcu
        have ht := latticeDist_triangle c u v
        have hcv : latticeDist c v ≤ a + 2 * D := by omega
        exact Or.inr ⟨b, v, hb, hvB, hxb,
          hbc.trans (latticeReach_single hc hvB hcv), Or.inl rfl⟩
    · have hvA : v ∈ A := huv.2.1.resolve_right hvB
      rcases ih with ⟨hxA, hxu⟩ | ⟨b, c, hb, hc, hxb, hbc, hcu⟩
      · exact Or.inl ⟨hxA,
          hxu.trans (latticeReach_single (latticeReach_mem hxA hxu) hvA huv.2.2)⟩
      · exact Or.inr ⟨b, c, hb, hc, hxb, hbc, componentTail_extend hcu hvA huv.2.2⟩

/-- The next set must be bounded at the enlarged step a+2D, not merely at D. -/
theorem componentDiameter_union {A B : Set Point} {D a b : ℕ}
    (hA : ComponentDiameter A D a) (hB : ComponentDiameter B (a + 2 * D) b) :
    ComponentDiameter (A ∪ B) D (b + 2 * a + 2 * D) := by
  intro x y hx _ hxy
  rcases union_reach_decomposition hA hx hxy with
    ⟨hxA, hxyA⟩ | ⟨u, v, hu, hv, hxu, huv, hvy⟩
  · have hd := hA hxA (latticeReach_mem hxA hxyA) hxyA
    omega
  · have huv' := hB hu hv huv
    have hvy' := componentTail_dist hA hvy
    have h1 := latticeDist_triangle x u y
    have h2 := latticeDist_triangle u v y
    omega

theorem hasBoundedComponents_union {A B : Set Point} {D a : ℕ}
    (hA : ComponentDiameter A D a) (hB : HasBoundedComponents B (a + 2 * D)) :
    HasBoundedComponents (A ∪ B) D := by
  obtain ⟨b, hb⟩ := hB
  exact ⟨b + 2 * a + 2 * D, componentDiameter_union hA hb⟩

end BinaryFormMoat.FiniteSieveIntegration

#print axioms BinaryFormMoat.FiniteSieveIntegration.latticeDist
#print axioms BinaryFormMoat.FiniteSieveIntegration.latticeDist_self
#print axioms BinaryFormMoat.FiniteSieveIntegration.latticeDist_symm
#print axioms BinaryFormMoat.FiniteSieveIntegration.latticeDist_triangle
#print axioms BinaryFormMoat.FiniteSieveIntegration.latticeDist_add_right
#print axioms BinaryFormMoat.FiniteSieveIntegration.latticeStep
#print axioms BinaryFormMoat.FiniteSieveIntegration.latticeReach
#print axioms BinaryFormMoat.FiniteSieveIntegration.latticeReach_refl
#print axioms BinaryFormMoat.FiniteSieveIntegration.latticeReach_single
#print axioms BinaryFormMoat.FiniteSieveIntegration.latticeReach_trans
#print axioms BinaryFormMoat.FiniteSieveIntegration.latticeReach_mem
#print axioms BinaryFormMoat.FiniteSieveIntegration.latticeReach_symm
#print axioms BinaryFormMoat.FiniteSieveIntegration.latticeReach_mono
#print axioms BinaryFormMoat.FiniteSieveIntegration.ComponentDiameter
#print axioms BinaryFormMoat.FiniteSieveIntegration.HasBoundedComponents
#print axioms BinaryFormMoat.FiniteSieveIntegration.componentTail
#print axioms BinaryFormMoat.FiniteSieveIntegration.componentTail_dist
#print axioms BinaryFormMoat.FiniteSieveIntegration.componentTail_extend
#print axioms BinaryFormMoat.FiniteSieveIntegration.union_reach_decomposition
#print axioms BinaryFormMoat.FiniteSieveIntegration.componentDiameter_union
#print axioms BinaryFormMoat.FiniteSieveIntegration.hasBoundedComponents_union
