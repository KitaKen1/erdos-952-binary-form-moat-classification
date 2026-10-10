import Moat.Basic
import Mathlib.NumberTheory.Zsqrtd.GaussianInt
import Mathlib.Algebra.MvPolynomial.Nilpotent

/-! Shared graph definitions and bridges for the two public proof entry points. -/

namespace BinaryFormMoatCatalogue

/-- Join distinct points at squared Euclidean distance at most $R$. -/
def stepGraph (S : Set (ℤ × ℤ)) (R : ℕ) : SimpleGraph S :=
  SimpleGraph.fromRel fun z w =>
    (z.val.1 - w.val.1)^2 + (z.val.2 - w.val.2)^2 ≤ (R : ℤ)

/-- All components at squared step bound $R$ have a common finite size bound. -/
def BoundedComponents (S : Set (ℤ × ℤ)) (R : ℕ) : Prop :=
  ∃ B : ℕ, ∀ z : S,
    Set.encard {w | (stepGraph S R).Reachable z w} ≤ (B : ℕ∞)

/-- A nonzero integer with at most $r$ distinct rational prime factors. -/
def FewPrimeFactors (r : ℕ) (n : ℤ) : Prop :=
  n ≠ 0 ∧ n.natAbs.primeFactors.card ≤ r

/-- An irreducible homogeneous binary form of degree at least two. -/
structure NonlinearIrreducibleForm where
  polynomial : MvPolynomial (Fin 2) ℤ
  irreducible : Irreducible polynomial
  homogeneous : polynomial.IsHomogeneous polynomial.totalDegree
  nonlinear : 2 ≤ polynomial.totalDegree

/-- The form's value at a point is nonzero and has at most $r$ distinct prime factors. -/
def NonlinearIrreducibleForm.FewPrimeFactors (F : NonlinearIrreducibleForm) (r : ℕ)
    (z : ℤ × ℤ) : Prop :=
  BinaryFormMoatCatalogue.FewPrimeFactors r (F.polynomial.eval ![z.1, z.2])

/-- The exceptional forms $c(aX+bY)^m$. -/
def IsLinearPower (F : MvPolynomial (Fin 2) ℤ) : Prop :=
  ∃ (c a b : ℤ) (m : ℕ), c ≠ 0 ∧ (a ≠ 0 ∨ b ≠ 0) ∧ 0 < m ∧
    F = MvPolynomial.C c *
      (MvPolynomial.C a * MvPolynomial.X (0 : Fin 2) +
       MvPolynomial.C b * MvPolynomial.X (1 : Fin 2)) ^ m

theorem graph_eq (F : MvPolynomial (Fin 2) ℤ) (r R : ℕ) :
    stepGraph {z | FewPrimeFactors r (F.eval ![z.1, z.2])} R =
      BinaryFormMoat.graph F r R := by
  ext z w
  have hs : (w.val.1 - z.val.1)^2 + (w.val.2 - z.val.2)^2 =
      (z.val.1 - w.val.1)^2 + (z.val.2 - w.val.2)^2 := by
    ring
  simp only [stepGraph, SimpleGraph.fromRel_adj, hs, or_self]
  rfl

theorem uniformMoat_iff (F : MvPolynomial (Fin 2) ℤ) :
    BinaryFormMoat.UniformMoat F ↔ ∀ R r : ℕ, BoundedComponents
      {z | FewPrimeFactors r (F.eval ![z.1, z.2])} R := by
  unfold BinaryFormMoat.UniformMoat BoundedComponents
  simp only [graph_eq]
  rfl

theorem stepGraph_adj {S : Set (ℤ × ℤ)} (R : ℕ) (z w : S) :
    (stepGraph S R).Adj z w ↔
      z ≠ w ∧ (z.val.1 - w.val.1)^2 + (z.val.2 - w.val.2)^2 ≤ (R : ℤ) := by
  have hs : (w.val.1 - z.val.1)^2 + (w.val.2 - z.val.2)^2 =
      (z.val.1 - w.val.1)^2 + (z.val.2 - w.val.2)^2 := by ring
  simp only [stepGraph, SimpleGraph.fromRel_adj, hs, or_self]

theorem boundedComponents_mono {S T : Set (ℤ × ℤ)} (hST : S ⊆ T)
    (R : ℕ) (hT : BoundedComponents T R) : BoundedComponents S R := by
  obtain ⟨B, hB⟩ := hT
  let inc : S → T := fun z => ⟨z.val, hST z.property⟩
  have hi : Function.Injective inc := by
    intro x y h
    have he : (inc x).val = (inc y).val := congrArg Subtype.val h
    exact Subtype.ext he
  let hom : stepGraph S R →g stepGraph T R :=
    { toFun := inc
      map_rel' := by
        intro x y h
        obtain ⟨hne, hd⟩ := (stepGraph_adj R x y).mp h
        exact (stepGraph_adj R (inc x) (inc y)).mpr ⟨fun he => hne (hi he), hd⟩ }
  refine ⟨B, fun z => le_trans ?_ (hB (inc z))⟩
  apply Set.encard_le_encard_of_injOn (f := inc)
  · intro w hw
    exact hw.map hom
  · exact hi.injOn

theorem nonlinear_not_isLinearPower (F : NonlinearIrreducibleForm) :
    ¬ BinaryFormMoat.IsLinearPower F.polynomial := by
  rintro ⟨c, a, b, m, hc, hab, hm, he⟩
  let L : MvPolynomial (Fin 2) ℤ :=
    MvPolynomial.C a * MvPolynomial.X 0 + MvPolynomial.C b * MvPolynomial.X 1
  have hL0 : L ≠ 0 := by
    intro h
    apply F.irreducible.ne_zero
    rw [he]
    change MvPolynomial.C c * L^m = 0
    rw [h, zero_pow hm.ne', mul_zero]
  have hLhom : L.IsHomogeneous 1 :=
    (MvPolynomial.isHomogeneous_C_mul_X a 0).add
      (MvPolynomial.isHomogeneous_C_mul_X b 1)
  have hLdeg : L.totalDegree = 1 := hLhom.totalDegree hL0
  have hLnu : ¬ IsUnit L := by
    intro hu
    have := (MvPolynomial.isUnit_iff_totalDegree_of_isReduced.mp hu).2
    omega
  have hpowNu : ¬ IsUnit (L^m) := (isUnit_pow_iff hm.ne').not.mpr hLnu
  have hCc : IsUnit (MvPolynomial.C c : MvPolynomial (Fin 2) ℤ) :=
    (F.irreducible.isUnit_or_isUnit he).resolve_right hpowNu
  have hpowIrr : Irreducible (L^m) :=
    (irreducible_isUnit_mul hCc).mp (he ▸ F.irreducible)
  have hm1 : m = 1 := by
    by_contra h
    exact not_irreducible_pow h hpowIrr
  have hdeg : F.polynomial.totalDegree ≤ 1 := by
    rw [he, hm1, pow_one]
    change (MvPolynomial.C c * L).totalDegree ≤ 1
    calc
      _ ≤ L.totalDegree := by
        simpa only [MvPolynomial.totalDegree_C, zero_add] using
          MvPolynomial.totalDegree_mul (MvPolynomial.C c) L
      _ = 1 := hLdeg
  exact (by omega : ¬ 2 ≤ F.polynomial.totalDegree) F.nonlinear

theorem gaussian_prime_norm_fewPrimeFactors (z : GaussianInt) (hz : Prime z) :
    FewPrimeFactors 1 z.norm := by
  have hn : z.norm.natAbs ≠ 0 :=
    Int.natAbs_ne_zero.mpr (mt GaussianInt.norm_eq_zero.mp hz.ne_zero)
  have hdiv : z ∣ (z.norm.natAbs : GaussianInt) := by
    rw [GaussianInt.natCast_natAbs_norm, Zsqrtd.norm_eq_mul_conj]
    exact dvd_mul_right _ _
  have extract (l : List ℕ) : z ∣ (l.prod : GaussianInt) →
      ∃ p ∈ l, z ∣ (p : GaussianInt) := by
    induction l with
    | nil => simp [hz.not_dvd_one]
    | cons p l ih =>
      intro h
      have hh : z ∣ (p : GaussianInt) * (l.prod : GaussianInt) := by simpa using h
      rcases hz.dvd_or_dvd hh with hp | hl
      · exact ⟨p, by simp, hp⟩
      · obtain ⟨q, hq, hd⟩ := ih hl
        exact ⟨q, by simp [hq], hd⟩
  obtain ⟨p, hp, hzp⟩ := extract z.norm.natAbs.primeFactorsList
    (by simpa only [Nat.prod_primeFactorsList hn] using hdiv)
  have hpPrime := Nat.prime_of_mem_primeFactorsList hp
  have hnorm : z.norm.natAbs ∣ p^2 := by
    obtain ⟨w, hw⟩ := hzp
    have he := congrArg (fun t : GaussianInt => t.norm.natAbs) hw
    refine ⟨w.norm.natAbs, ?_⟩
    simpa [Zsqrtd.norm_natCast, Zsqrtd.norm_mul, Int.natAbs_mul, sq] using he
  refine ⟨Int.natAbs_ne_zero.mp hn, ?_⟩
  have hc := Finset.card_le_card (Nat.primeFactors_mono hnorm (pow_ne_zero 2 hpPrime.ne_zero))
  simpa [Nat.primeFactors_prime_pow (by decide : 2 ≠ 0) hpPrime] using hc

/-- A uniform component-size bound rules out arbitrarily long injective prefixes. -/
theorem no_arbitrarily_long_walks (S : Set (ℤ × ℤ)) (C : ℤ)
    (hS : BoundedComponents S C.natAbs) :
    ¬ ∀ N : ℕ, ∃ x : ℕ → GaussianInt,
      Function.Injective x ∧
        ∀ n ≤ N, ((x n).re, (x n).im) ∈ S ∧
          (n < N → (x (n + 1) - x n).norm < C) := by
  rintro hwalk
  obtain ⟨B, hB⟩ := hS
  obtain ⟨x, hx, hwalk⟩ := hwalk B
  let v : Fin (B + 1) → S := fun i =>
    ⟨((x i).re, (x i).im), (hwalk i (by omega)).1⟩
  have hv : Function.Injective v := by
    intro i j hij
    apply Fin.ext
    apply hx
    have h := congrArg Subtype.val hij
    apply Zsqrtd.ext
    · exact congrArg Prod.fst h
    · exact congrArg Prod.snd h
  have reach (n : ℕ) (hn : n ≤ B) :
      (stepGraph S C.natAbs).Reachable (v ⟨0, by omega⟩) (v ⟨n, by omega⟩) := by
    induction n with
    | zero => exact SimpleGraph.Reachable.refl _
    | succ n ih =>
      apply (ih (by omega)).trans
      apply SimpleGraph.Adj.reachable
      apply (stepGraph_adj _ _ _).mpr
      constructor
      · intro he
        have hne := congrArg Fin.val (hv he)
        change n = n + 1 at hne
        omega
      · have hs := (hwalk n (by omega)).2 (by omega)
        have he :
            ((x n).re - (x (n + 1)).re)^2 +
              ((x n).im - (x (n + 1)).im)^2 = (x (n + 1) - x n).norm := by
          simp only [Zsqrtd.norm, Zsqrtd.re_sub, Zsqrtd.im_sub]
          ring
        change ((x n).re - (x (n + 1)).re)^2 +
          ((x n).im - (x (n + 1)).im)^2 ≤ (C.natAbs : ℤ)
        rw [he]
        exact hs.le.trans Int.le_natAbs
  have hcard : ((B + 1 : ℕ) : ℕ∞) ≤
      Set.encard {w | (stepGraph S C.natAbs).Reachable (v ⟨0, by omega⟩) w} := by
    calc
      _ = (Set.univ : Set (Fin (B + 1))).encard := by
        simp [Set.encard_univ, ENat.card_eq_coe_fintype_card]
      _ ≤ _ := Set.encard_le_encard_of_injOn
        (f := v) (by intro i _; exact reach i (by omega)) hv.injOn
  have hbad : B + 1 ≤ B := by
    exact_mod_cast hcard.trans (hB (v ⟨0, by omega⟩))
  omega

end BinaryFormMoatCatalogue
