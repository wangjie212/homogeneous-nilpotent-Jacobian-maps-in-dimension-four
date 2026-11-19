import DimensionFourDependence.RationalGraphResidueAlgebra
import Mathlib.FieldTheory.RatFunc.AsPolynomial

/-! # The original rational graph carries the unspecialized level field -/

namespace DimensionFourDependence

open Polynomial

set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 100000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {k R F : Type*} [Field k] [CommRing R] [IsDomain R] [IsLocalRing R]
  [Field F] [Algebra k R] [Algebra R F]
  (f : F)

/-- The original scalar polynomial parameter acts on the actual
graph by the same original coefficient map and the original function f. -/
noncomputable def rationalGraphScalarPolynomialHom : Polynomial k →+* rationalGraphAlgebra R f :=
  (rationalGraphPolynomialHom R f).toRingHom.comp (Polynomial.mapRingHom (algebraMap k R))

variable (hker : RingHom.ker (Polynomial.aeval f).toRingHom ≤
  RingHom.ker (Polynomial.mapRingHom (IsLocalRing.residue R)))

/-- The actual graph residue keeps the scalar polynomial parameter
as a polynomial variable over the original local residue field. -/
theorem rationalGraphResidueHom_scalar_polynomial (P : Polynomial k) :
    rationalGraphResidueHom R f hker (rationalGraphScalarPolynomialHom (k := k) f P) =
      P.map ((IsLocalRing.residue R).comp (algebraMap k R)) := by
  change rationalGraphResidueHom R f hker
    (rationalGraphPolynomialHom R f (P.map (algebraMap k R))) = _
  rw [rationalGraphResidueHom_polynomial, Polynomial.map_map]

/-- Every nonzero scalar polynomial stays nonzero at the graph prime
above the original local closed point. Thus no scalar level is chosen. -/
theorem rationalGraphResiduePrime_scalar_polynomial_not_mem
    (P : Polynomial k) (hP : P ≠ 0) :
    rationalGraphScalarPolynomialHom (k := k) f P ∉
      (rationalGraphResiduePrime R f hker).asIdeal := by
  change rationalGraphResidueHom R f hker (rationalGraphScalarPolynomialHom (k := k) f P) ≠ 0
  rw [rationalGraphResidueHom_scalar_polynomial]
  exact fun he => hP ((Polynomial.map_injective _
    ((IsLocalRing.residue R).comp (algebraMap k R)).injective) (he.trans (Polynomial.map_zero _).symm))

variable [Algebra k F] [IsScalarTower k R F]

/-- The scalar polynomial action has exactly its original actual
function-field value under the original coefficient tower. -/
theorem rationalGraphScalarPolynomialHom_value (P : Polynomial k) :
    (rationalGraphScalarPolynomialHom (R := R) f P : F) = Polynomial.aeval f P := by
  change Polynomial.aeval f (P.map (algebraMap k R)) = Polynomial.aeval f P
  exact (Polynomial.aeval_eq_aeval_map (IsScalarTower.algebraMap_eq k R F).symm P f).symm

include hker

/-- The graph's free residue parameter proves that f is actually
transcendental over the original coefficient field. -/
theorem rationalGraph_parameter_transcendental : Transcendental k f := by
  rw [transcendental_iff]
  intro P hP
  by_contra hP0
  apply rationalGraphResiduePrime_scalar_polynomial_not_mem f hker P hP0
  have hzero : rationalGraphScalarPolynomialHom (R := R) f P = 0 := by
    apply Subtype.ext
    exact (rationalGraphScalarPolynomialHom_value f P).trans hP
  rw [hzero]
  exact Ideal.zero_mem _

/-- The unspecialized rational level field embeds into the original
function field, with its variable mapped to exactly f. -/
noncomputable def rationalGraphParameterFieldHom : RatFunc k →ₐ[k] F :=
  RatFunc.liftAlgHom (Polynomial.aeval f)
    (nonZeroDivisors_le_comap_nonZeroDivisors_of_injective _
      (transcendental_iff_injective.mp (rationalGraph_parameter_transcendental f hker)))

/-- The embedding retains the actual rational function as its
parameter value, without an independently chosen transcendental element. -/
theorem rationalGraphParameterFieldHom_X : rationalGraphParameterFieldHom (k := k) (R := R) f hker RatFunc.X = f := by
  unfold rationalGraphParameterFieldHom
  change RatFunc.liftRingHom (Polynomial.aeval f).toRingHom _ RatFunc.X = f
  rw [RatFunc.liftRingHom_X]
  exact Polynomial.aeval_X f

end DimensionFourDependence
