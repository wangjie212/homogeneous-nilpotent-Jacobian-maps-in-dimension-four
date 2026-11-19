import DimensionFourDependence.NormalGraphResidueKernel
import Mathlib.RingTheory.Ideal.Quotient.Operations

/-! # The actual rational graph has a residue-polynomial specialization -/

namespace DimensionFourDependence

open Polynomial

set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 100000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable (R : Type*) {F : Type*} [CommRing R] [IsDomain R] [IsLocalRing R]
  [Field F] [Algebra R F]

/-- The algebra of the actual rational graph, inside the specified
original field: it is the image of actual evaluation at f. -/
noncomputable def rationalGraphAlgebra (f : F) : Subalgebra R F := (Polynomial.aeval f).range

/-- Actual polynomial evaluation onto the original graph algebra. -/
noncomputable def rationalGraphPolynomialHom (f : F) : Polynomial R →ₐ[R] rationalGraphAlgebra R f :=
  (Polynomial.aeval f).rangeRestrict

/-- This presentation contains every graph function, with its actual
field value rather than an independently chosen coordinate ring. -/
theorem rationalGraphPolynomialHom_surjective (f : F) :
    Function.Surjective (rationalGraphPolynomialHom R f) :=
  (Polynomial.aeval f).rangeRestrict_surjective

/-- The graph presentation keeps every original coefficient. -/
theorem rationalGraphPolynomialHom_C (f : F) (r : R) :
    rationalGraphPolynomialHom R f (Polynomial.C r) = algebraMap R (rationalGraphAlgebra R f) r := by
  apply Subtype.ext
  exact Polynomial.aeval_C f r

/-- The graph parameter is the original element f of the original field. -/
theorem rationalGraphPolynomialHom_X_value (f : F) :
    (rationalGraphPolynomialHom R f Polynomial.X : F) = f := Polynomial.aeval_X f

variable (f : F)
    (hker : RingHom.ker (Polynomial.aeval f).toRingHom ≤
      RingHom.ker (Polynomial.mapRingHom (IsLocalRing.residue R)))

/-- Coefficientwise residue descends to the actual graph algebra
because every relation has zero residue polynomial. -/
noncomputable def rationalGraphResidueHom :
    rationalGraphAlgebra R f →+* Polynomial (IsLocalRing.ResidueField R) :=
  RingHom.liftOfSurjective (rationalGraphPolynomialHom R f).toRingHom
    (rationalGraphPolynomialHom_surjective R f)
    ⟨Polynomial.mapRingHom (IsLocalRing.residue R), by
      intro P hP
      apply hker
      change Polynomial.aeval f P = 0
      exact congrArg Subtype.val hP⟩

/-- Descending coefficientwise residue preserves the entire actual
polynomial presentation, including its free parameter. -/
theorem rationalGraphResidueHom_polynomial (P : Polynomial R) :
    rationalGraphResidueHom R f hker (rationalGraphPolynomialHom R f P) =
      P.map (IsLocalRing.residue R) := by
  exact RingHom.liftOfSurjective_comp_apply _ _ _ P

/-- The graph's original local coefficients reduce by the original
local residue map, with no change in coefficient realization. -/
theorem rationalGraphResidueHom_coefficient (r : R) :
    rationalGraphResidueHom R f hker (algebraMap R (rationalGraphAlgebra R f) r) =
      Polynomial.C (IsLocalRing.residue R r) := by
  rw [← rationalGraphPolynomialHom_C R f r, rationalGraphResidueHom_polynomial, Polynomial.map_C]

/-- The original rational function specializes to an independent
polynomial parameter at the graph point above the original closed point. -/
theorem rationalGraphResidueHom_parameter :
    rationalGraphResidueHom R f hker (rationalGraphPolynomialHom R f Polynomial.X) = Polynomial.X := by
  rw [rationalGraphResidueHom_polynomial, Polynomial.map_X]

/-- The prime above the original closed point, with the graph
parameter still free in its residue domain. -/
noncomputable def rationalGraphResiduePrime : PrimeSpectrum (rationalGraphAlgebra R f) :=
  ⟨RingHom.ker (rationalGraphResidueHom R f hker), RingHom.ker_isPrime _⟩

/-- The constructed actual graph prime contracts to exactly the
original local maximal ideal. -/
theorem rationalGraphResiduePrime_under :
    (rationalGraphResiduePrime R f hker).asIdeal.comap
      (algebraMap R (rationalGraphAlgebra R f)) = IsLocalRing.maximalIdeal R := by
  ext r
  change rationalGraphResidueHom R f hker (algebraMap R (rationalGraphAlgebra R f) r) = 0 ↔ _
  rw [rationalGraphResidueHom_coefficient, Polynomial.C_eq_zero, IsLocalRing.residue_eq_zero_iff]

/-- The constructed graph point belongs to the actual generic-level
parameter open, not to the zero level of the rational function. -/
theorem rationalGraphResiduePrime_parameter_not_mem :
    rationalGraphPolynomialHom R f Polynomial.X ∉ (rationalGraphResiduePrime R f hker).asIdeal := by
  change rationalGraphResidueHom R f hker (rationalGraphPolynomialHom R f Polynomial.X) ≠ 0
  rw [rationalGraphResidueHom_parameter]
  exact Polynomial.X_ne_zero

end DimensionFourDependence
