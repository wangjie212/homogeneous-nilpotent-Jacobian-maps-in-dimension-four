import DimensionFourDependence.PrimeContractionModelTransfer

/-! # Consequences of orders at the given source-divisor prime

The prime and original-source action remain fixed while its constructed
parameter data is used to derive a consequence of the section orders.
This permits the normalization model to supply data from that same prime.
-/

namespace DimensionFourDependence

variable {R T ι : Type*} [CommRing R] [CommRing T] [Algebra R T]

/-- At every given prime over the source divisor, the stated source
section order bounds imply the full asserted consequence. -/
def PrimesOverSourceOrdersImply (Q : Ideal R) (x : ι → R) (a : ℕ) (C : Prop) : Prop :=
  ∀ (q : Ideal T) [q.IsPrime] [q.LiesOver Q],
    (∀ i, algebraMap R (Localization.AtPrime q) (x i) ∈
      (IsLocalRing.maximalIdeal (Localization.AtPrime q)) ^ a) → C

/-- Data constructed from the given prime can establish its order
consequence without assuming that data independently. -/
theorem prime_local_order_consequence_of_models
    (Q : Ideal R) (x : ι → R) (a : ℕ) (C : Prop) {M : Prop}
    (hmodels : PrimesOverSourceSatisfy (T := T) Q M)
    (hconsequence : M → PrimesOverSourceOrdersImply (T := T) Q x a C) :
    PrimesOverSourceOrdersImply (T := T) Q x a C := by
  intro q hq hlie horder
  have h := hconsequence (@hmodels q hq hlie)
  exact @h q hq hlie horder

end DimensionFourDependence
