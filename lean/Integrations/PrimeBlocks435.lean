import Integrations.PeriodicFinite435

namespace BinaryFormMoat.FiniteSieveIntegration

def avoidPrimes (F : Form) (P : Finset ℕ) : Set Point :=
  {z | ∀ p ∈ P, ¬p ∣ (value F z).natAbs}

def primePeriod (P : Finset ℕ) : ℕ := ∏ p ∈ P, p

theorem primePeriod_pos {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime) :
    0 < primePeriod P := by
  exact Finset.prod_pos (fun p hp => (hP p hp).pos)

theorem prime_dvd_period {P : Finset ℕ} {p : ℕ} (hp : p ∈ P) :
    p ∣ primePeriod P := Finset.dvd_prod_of_mem id hp

theorem avoidPrimes_periodic (F : Form) (P : Finset ℕ) :
    PeriodicSet (primePeriod P) (avoidPrimes F P) := by
  intro x y hxy
  have hcast (p : ℕ) (hp : p ∈ P) :
      (value F x : ZMod p) = (value F y : ZMod p) :=
    value_cast_congr F p x y (residue_eq_of_dvd (prime_dvd_period hp) x y hxy)
  have hdvd (p : ℕ) (hp : p ∈ P) :
      p ∣ (value F x).natAbs ↔ p ∣ (value F y).natAbs := by
    rw [← Int.natCast_dvd, ← Int.natCast_dvd,
      ← ZMod.intCast_zmod_eq_zero_iff_dvd, ← ZMod.intCast_zmod_eq_zero_iff_dvd, hcast p hp]
  exact forall_congr' (fun p => forall_congr' (fun hp => not_congr (hdvd p hp)))

/-- A concrete finite-sieve interface. Finite components are sufficient;
the remaining entropy proof must supply this input, or a stronger bound. -/
def FiniteComponentSieve (F : Form) : Prop :=
  ∀ D (S : Finset ℕ), ∃ P : Finset ℕ,
    (∀ p ∈ P, p.Prime) ∧ Disjoint P S ∧ FiniteComponents (avoidPrimes F P) D

def BoundedComponentSieve (F : Form) : Prop :=
  ∀ D (S : Finset ℕ), ∃ P : Finset ℕ,
    (∀ p ∈ P, p.Prime) ∧ Disjoint P S ∧ HasBoundedComponents (avoidPrimes F P) D

theorem boundedComponentSieve_of_finiteComponentSieve (F : Form)
    (hF : FiniteComponentSieve F) : BoundedComponentSieve F := by
  intro D S
  obtain ⟨P, hP, hPS, hfin⟩ := hF D S
  let : NeZero (primePeriod P) := ⟨(primePeriod_pos hP).ne'⟩
  exact ⟨P, hP, hPS, periodic_hasBoundedComponents (avoidPrimes_periodic F P) hfin⟩

def blockPrimeUnion {n : ℕ} (P : Fin n → Finset ℕ) : Finset ℕ :=
  Finset.univ.biUnion P

def blockAvoid {n : ℕ} (F : Form) (P : Fin n → Finset ℕ) : Set Point :=
  {z | ∃ i, z ∈ avoidPrimes F (P i)}

theorem block_subset_union {n : ℕ} (P : Fin n → Finset ℕ) (i : Fin n) :
    P i ⊆ blockPrimeUnion P := by
  intro p hp
  exact Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ i, hp⟩

theorem blockAvoid_cons {n : ℕ} (F : Form) (Q : Finset ℕ) (P : Fin n → Finset ℕ) :
    blockAvoid F (Fin.cons Q P) = avoidPrimes F Q ∪ blockAvoid F P := by
  ext z
  simp only [blockAvoid, Set.mem_ofPred_eq, Set.mem_union, Fin.exists_fin_succ,
    Fin.cons_zero, Fin.cons_succ]

/-- Choose the next block at the enlarged step bound and exclude all earlier
blocks. Pairwise disjointness is retained even when a block happens to be empty. -/
theorem exists_disjoint_bounded_blocks (F : Form) (hF : BoundedComponentSieve F)
    (D n : ℕ) (S : Finset ℕ) :
    ∃ P : Fin n → Finset ℕ,
      (∀ i, ∀ p ∈ P i, p.Prime) ∧
      (∀ i, Disjoint (P i) S) ∧
      Pairwise (fun i j => Disjoint (P i) (P j)) ∧
      HasBoundedComponents (blockAvoid F P) D := by
  classical
  induction n with
  | zero =>
    refine ⟨Fin.elim0, ?_, ?_, ?_, 0, ?_⟩
    · intro i; exact Fin.elim0 i
    · intro i; exact Fin.elim0 i
    · intro i; exact Fin.elim0 i
    · intro x _ hx; rcases hx with ⟨i, _⟩; exact Fin.elim0 i
  | succ n ih =>
    obtain ⟨P, hP, hPS, hdis, a, hA⟩ := ih
    obtain ⟨Q, hQ, hQS, b, hB⟩ := hF (a + 2 * D) (S ∪ blockPrimeUnion P)
    have hQS' : Disjoint Q S := hQS.mono_right Finset.subset_union_left
    have hQP (i : Fin n) : Disjoint Q (P i) :=
      hQS.mono_right ((block_subset_union P i).trans Finset.subset_union_right)
    refine ⟨Fin.cons Q P, ?_, ?_, ?_, b + 2 * a + 2 * D, ?_⟩
    · intro i
      cases i using Fin.cases with
      | zero => exact hQ
      | succ i => exact hP i
    · intro i
      cases i using Fin.cases with
      | zero => exact hQS'
      | succ i => exact hPS i
    · intro i j hij
      cases i using Fin.cases with
      | zero =>
        cases j using Fin.cases with
        | zero => exact (hij rfl).elim
        | succ j => exact hQP j
      | succ i =>
        cases j using Fin.cases with
        | zero => exact (hQP i).symm
        | succ j => exact hdis (by intro h; apply hij; simpa [h])
    · rw [blockAvoid_cons, Set.union_comm]
      exact componentDiameter_union hA hB

/-- Failure to avoid every block supplies one DISTINCT rational prime per
block; this is a pigeonhole argument, not a sum over root coordinates. -/
theorem allowed_mem_blockAvoid (F : Form) (r : ℕ)
    (P : Fin (r + 1) → Finset ℕ)
    (hP : ∀ i, ∀ p ∈ P i, p.Prime)
    (hdis : Pairwise (fun i j => Disjoint (P i) (P j)))
    (z : Point) (hz : Allowed F r z) : z ∈ blockAvoid F P := by
  classical
  by_contra hnone
  have hex (i : Fin (r + 1)) : ∃ p, p ∈ P i ∧ p ∣ (value F z).natAbs := by
    by_contra h
    apply hnone
    refine ⟨i, ?_⟩
    intro p hp hd
    exact h ⟨p, hp, hd⟩
  choose p hp hd using hex
  let f (i : Fin (r + 1)) : ↥((value F z).natAbs.primeFactors) :=
    ⟨p i, (hP i (p i) (hp i)).mem_primeFactors (hd i) (Int.natAbs_ne_zero.mpr hz.1)⟩
  have hinj : Function.Injective f := by
    intro i j hij
    by_contra hne
    have he : p i = p j := congrArg Subtype.val hij
    exact Finset.disjoint_left.mp (hdis hne) (hp i) (he.symm ▸ hp j)
  have hc := Fintype.card_le_of_injective f hinj
  simp only [Fintype.card_fin, Fintype.card_coe] at hc
  have hb : (value F z).natAbs.primeFactors.card ≤ r := hz.2
  omega

end BinaryFormMoat.FiniteSieveIntegration

#print axioms BinaryFormMoat.FiniteSieveIntegration.avoidPrimes
#print axioms BinaryFormMoat.FiniteSieveIntegration.primePeriod
#print axioms BinaryFormMoat.FiniteSieveIntegration.primePeriod_pos
#print axioms BinaryFormMoat.FiniteSieveIntegration.prime_dvd_period
#print axioms BinaryFormMoat.FiniteSieveIntegration.avoidPrimes_periodic
#print axioms BinaryFormMoat.FiniteSieveIntegration.FiniteComponentSieve
#print axioms BinaryFormMoat.FiniteSieveIntegration.BoundedComponentSieve
#print axioms BinaryFormMoat.FiniteSieveIntegration.boundedComponentSieve_of_finiteComponentSieve
#print axioms BinaryFormMoat.FiniteSieveIntegration.blockPrimeUnion
#print axioms BinaryFormMoat.FiniteSieveIntegration.blockAvoid
#print axioms BinaryFormMoat.FiniteSieveIntegration.block_subset_union
#print axioms BinaryFormMoat.FiniteSieveIntegration.blockAvoid_cons
#print axioms BinaryFormMoat.FiniteSieveIntegration.exists_disjoint_bounded_blocks
#print axioms BinaryFormMoat.FiniteSieveIntegration.allowed_mem_blockAvoid
