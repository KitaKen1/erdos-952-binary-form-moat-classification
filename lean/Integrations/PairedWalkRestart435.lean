import Integrations.PaperMiddleTailTransfer435

noncomputable section
namespace BinaryFormMoat.GeometryIntegration
open EntropyIntegration MeasureTheory ProbabilityTheory

/-- Equality of history lengths transports the retained source, without dropping data. -/
def pairedWalkCast {A : Type*} (N : ℕ → ℕ) (n n' : ℕ) (h : n = n') :
    PairedWalkSource A N n → PairedWalkSource A N n' := cast (congrArg (PairedWalkSource A N) h)

theorem pairedWalkCast_time {A : Type*} (N : ℕ → ℕ) (b : A → ℕ) (n n' : ℕ)
    (h : n = n') (ω : PairedWalkSource A N n) :
    pairedWalkTime N b n' (pairedWalkCast N n n' h ω) = pairedWalkTime N b n ω := by
  subst n'
  rfl

variable {A : Type*} [Fintype A] [MeasurableSpace A]

/-- Naturality of the ACTUAL pair-plus-coin transition under length equality. -/
theorem pairedWalkStep_map_cast (z : ℕ → Point) (N : ℕ → ℕ) (b : A → ℕ)
    (n n' : ℕ) (h : n = n') (μ : Measure (PairedWalkSource A N n)) :
    (fairEndpointLaw (differencePairForwardLaw z (N n) μ (pairedWalkTime N b n))).map
      (pairedWalkCast N (n + 1) (n' + 1) (congrArg (fun a => a + 1) h)) =
        fairEndpointLaw (differencePairForwardLaw z (N n')
          (μ.map (pairedWalkCast N n n' h)) (pairedWalkTime N b n')) := by
  subst n'
  change (fairEndpointLaw (differencePairForwardLaw z (N n) μ (pairedWalkTime N b n))).map id =
    fairEndpointLaw (differencePairForwardLaw z (N n) (μ.map id) (pairedWalkTime N b n))
  rw [Measure.map_id, Measure.map_id]

/-- An arbitrary starting history law continues by the SAME original windows.
The only map is the associativity cast of the complete retained history. -/
theorem pairedWalkTailLaw_restart (z : ℕ → Point) (N : ℕ → ℕ) (b : A → ℕ)
    (k : ℕ) (ν : Measure (PairedWalkSource A N k)) (j r : ℕ) :
    (pairedWalkTailLaw z N b k ν (j + r)).map
      (pairedWalkCast N (k + (j + r)) ((k + j) + r) (Nat.add_assoc k j r).symm) =
        pairedWalkTailLaw z N b (k + j) (pairedWalkTailLaw z N b k ν j) r := by
  induction r with
  | zero =>
    change (pairedWalkTailLaw z N b k ν j).map id = pairedWalkTailLaw z N b k ν j
    exact Measure.map_id
  | succ r ih =>
    change (fairEndpointLaw (differencePairForwardLaw z (N (k + (j + r)))
      (pairedWalkTailLaw z N b k ν (j + r)) (pairedWalkTime N b (k + (j + r))))).map
        (pairedWalkCast N (k + (j + r) + 1) ((k + j) + r + 1)
          (congrArg (fun a => a + 1) (Nat.add_assoc k j r).symm)) =
          fairEndpointLaw (differencePairForwardLaw z (N ((k + j) + r))
            (pairedWalkTailLaw z N b (k + j) (pairedWalkTailLaw z N b k ν j) r)
            (pairedWalkTime N b ((k + j) + r)))
    rw [pairedWalkStep_map_cast z N b (k + (j + r)) ((k + j) + r) (Nat.add_assoc k j r).symm, ih]

end BinaryFormMoat.GeometryIntegration
#print axioms BinaryFormMoat.GeometryIntegration.pairedWalkCast
#print axioms BinaryFormMoat.GeometryIntegration.pairedWalkCast_time
#print axioms BinaryFormMoat.GeometryIntegration.pairedWalkStep_map_cast
#print axioms BinaryFormMoat.GeometryIntegration.pairedWalkTailLaw_restart
