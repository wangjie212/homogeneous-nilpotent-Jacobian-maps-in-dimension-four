import DimensionFourDependence.Defs
import Mathlib.RingTheory.Ideal.Over

/-! # Transfer a prime-local model through actual prime contraction

Keeping the complete quantified statement separate lets a concrete
normalization use an original-coordinate prime model without expanding
the model's coordinate rings while eliminating existential witnesses.
-/

namespace DimensionFourDependence

variable {R S T : Type*} [CommRing R] [CommRing S] [CommRing T]
  [Algebra R S] [Algebra R T] [Algebra S T]

/-- Every given upstairs prime over the original source satisfies the
stated complete local-model conclusion. -/
def PrimesOverSourceSatisfy (Q : Ideal R) (M : Prop) : Prop :=
  ∀ (q : Ideal T) [q.IsPrime] [q.LiesOver Q], M

/-- Actual contraction transfers a model for original coordinate primes
to every given normalization prime over that same source prime. -/
theorem prime_models_transfer_of_contraction (Q : Ideal R) {M : Prop}
    (hcontract : ∀ (q : Ideal T) [q.IsPrime] [q.LiesOver Q], (q.under S).LiesOver Q)
    (hmodel : PrimesOverSourceSatisfy (T := S) Q M) :
    PrimesOverSourceSatisfy (T := T) Q M := by
  intro q hq hlie
  let P := q.under S
  have hP : P.IsPrime := inferInstance
  exact @hmodel P hP (@hcontract q hq hlie)

end DimensionFourDependence
