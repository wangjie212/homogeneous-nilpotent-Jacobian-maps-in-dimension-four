import DimensionFourDependence.RationalGraphGenericParameter

/-! # The generic graph point has a local ring containing the actual level field -/

namespace DimensionFourDependence

open Polynomial

set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 100000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable (R : Type*) {F : Type*} [CommRing R] [IsDomain R] [IsLocalRing R]
  [Field F] [Algebra R F] [IsFractionRing R F]

/-- The actual original field is also a fraction field of its
intermediate graph algebra, with the original inclusions. -/
theorem rationalGraphAlgebra_isFractionRing (f : F) :
    IsFractionRing (rationalGraphAlgebra R f) F := by
  apply IsFractionRing.of_field
  intro z
  obtain ⟨a, b, hb, he⟩ := IsFractionRing.div_surjective R z
  refine ⟨algebraMap R (rationalGraphAlgebra R f) a,
    algebraMap R (rationalGraphAlgebra R f) b, ?_⟩
  change z = algebraMap R F a / algebraMap R F b
  exact he.symm

attribute [instance] rationalGraphAlgebra_isFractionRing

variable (f : F)
  (hker : RingHom.ker (Polynomial.aeval f).toRingHom ≤
    RingHom.ker (Polynomial.mapRingHom (IsLocalRing.residue R)))

/-- The local ring of the constructed generic graph point, realized
inside the same actual original field. -/
noncomputable def rationalGraphLocalAlgebra : Subalgebra (rationalGraphAlgebra R f) F :=
  fractionPrimeLocalAlgebra (rationalGraphAlgebra R f) (rationalGraphResiduePrime R f hker).asIdeal

/-- The constructed graph local ring is genuinely local. -/
theorem rationalGraphLocalAlgebra_isLocalRing : IsLocalRing (rationalGraphLocalAlgebra R f hker) :=
  fractionPrimeLocalAlgebra_isLocalRing _ _

/-- Its actual coefficient algebra localization is at the exact
constructed graph prime. -/
theorem rationalGraphLocalAlgebra_isLocalization :
    IsLocalization.AtPrime (rationalGraphLocalAlgebra R f hker)
      (rationalGraphResiduePrime R f hker).asIdeal :=
  fractionPrimeLocalAlgebra_isLocalization _ _

attribute [instance] rationalGraphLocalAlgebra_isLocalRing rationalGraphLocalAlgebra_isLocalization

/-- The original local coefficient ring maps to this actual graph
local ring by its two original inclusions. -/
noncomputable def rationalGraphLocalCoefficientHom : R →+* rationalGraphLocalAlgebra R f hker :=
  (algebraMap (rationalGraphAlgebra R f) (rationalGraphLocalAlgebra R f hker)).comp
    (algebraMap R (rationalGraphAlgebra R f))

/-- The original graph residue map extends to the graph local ring
and the rational function field of its residue polynomial parameter. -/
noncomputable def rationalGraphLocalResidueHom :
    rationalGraphLocalAlgebra R f hker →+* RatFunc (IsLocalRing.ResidueField R) :=
  IsLocalization.lift (M := (rationalGraphResiduePrime R f hker).asIdeal.primeCompl)
    (S := rationalGraphLocalAlgebra R f hker)
    (g := (algebraMap (Polynomial (IsLocalRing.ResidueField R))
      (RatFunc (IsLocalRing.ResidueField R))).comp (rationalGraphResidueHom R f hker)) (by
      intro y
      apply isUnit_iff_ne_zero.mpr
      apply (map_ne_zero_iff _ (IsFractionRing.injective
        (Polynomial (IsLocalRing.ResidueField R)) (RatFunc (IsLocalRing.ResidueField R)))).mpr
      exact y.property)

/-- Every graph coefficient keeps its exact residue value after
passing to the actual graph local ring. -/
theorem rationalGraphLocalResidueHom_graph_coefficient (a : rationalGraphAlgebra R f) :
    rationalGraphLocalResidueHom R f hker
      (algebraMap (rationalGraphAlgebra R f) (rationalGraphLocalAlgebra R f hker) a) =
      algebraMap (Polynomial (IsLocalRing.ResidueField R)) (RatFunc (IsLocalRing.ResidueField R))
        (rationalGraphResidueHom R f hker a) := by
  exact IsLocalization.lift_eq _ a

/-- Original local coefficients specialize by the original residue
map, as constant rational functions in the free level parameter. -/
theorem rationalGraphLocalResidueHom_original_coefficient (r : R) :
    rationalGraphLocalResidueHom R f hker (rationalGraphLocalCoefficientHom R f hker r) =
      RatFunc.C (IsLocalRing.residue R r) := by
  rw [rationalGraphLocalCoefficientHom, RingHom.comp_apply,
    rationalGraphLocalResidueHom_graph_coefficient, rationalGraphResidueHom_coefficient]
  exact RatFunc.algebraMap_C _

/-- Vanishing of an original coefficient at the original closed
point is retained in the constructed generic graph specialization. -/
theorem rationalGraphLocalCoefficientHom_mem_maximal_iff (r : R) :
    rationalGraphLocalCoefficientHom R f hker r ∈
      IsLocalRing.maximalIdeal (rationalGraphLocalAlgebra R f hker) ↔
      r ∈ IsLocalRing.maximalIdeal R := by
  rw [rationalGraphLocalCoefficientHom, RingHom.comp_apply,
    IsLocalization.AtPrime.to_map_mem_maximal_iff (rationalGraphLocalAlgebra R f hker)
      (rationalGraphResiduePrime R f hker).asIdeal]
  change r ∈ (rationalGraphResiduePrime R f hker).asIdeal.comap
    (algebraMap R (rationalGraphAlgebra R f)) ↔ _
  rw [rationalGraphResiduePrime_under]

variable {k : Type*} [Field k] [Algebra k R]

/-- Every nonzero polynomial in the scalar parameter is invertible
at the generic graph point. This constructs the actual rational level
field inside the same original graph local ring. -/
noncomputable def rationalGraphLocalParameterHom : RatFunc k →+* rationalGraphLocalAlgebra R f hker :=
  IsLocalization.lift (M := nonZeroDivisors (Polynomial k)) (S := RatFunc k)
    (g := (algebraMap (rationalGraphAlgebra R f) (rationalGraphLocalAlgebra R f hker)).comp
      (rationalGraphScalarPolynomialHom (k := k) f)) (by
      intro y
      have hy0 : (y : Polynomial k) ≠ 0 := mem_nonZeroDivisors_iff_ne_zero.mp y.property
      have hyq : rationalGraphScalarPolynomialHom (k := k) (R := R) f (y : Polynomial k) ∉
          (rationalGraphResiduePrime R f hker).asIdeal :=
        rationalGraphResiduePrime_scalar_polynomial_not_mem (k := k) (R := R) f hker
          (y : Polynomial k) hy0
      let yC : (rationalGraphResiduePrime R f hker).asIdeal.primeCompl :=
        ⟨rationalGraphScalarPolynomialHom (k := k) (R := R) f (y : Polynomial k), by
          change rationalGraphScalarPolynomialHom (k := k) (R := R) f (y : Polynomial k) ∉ _
          exact hyq⟩
      exact IsLocalization.map_units (rationalGraphLocalAlgebra R f hker) yC)

/-- The local generic parameter field retains the original scalar
coefficient map into the original local ring. -/
theorem rationalGraphLocalParameterHom_C (c : k) :
    rationalGraphLocalParameterHom (k := k) R f hker (RatFunc.C c) =
      rationalGraphLocalCoefficientHom R f hker (algebraMap k R c) := by
  rw [rationalGraphLocalParameterHom, ← RatFunc.algebraMap_C, IsLocalization.lift_eq]
  change algebraMap (rationalGraphAlgebra R f) (rationalGraphLocalAlgebra R f hker)
    (rationalGraphPolynomialHom R f ((Polynomial.C c).map (algebraMap k R))) = _
  rw [Polynomial.map_C, rationalGraphPolynomialHom_C]
  rfl

/-- The constructed field embedding maps its generic parameter to
the original rational function, as an actual local graph element. -/
theorem rationalGraphLocalParameterHom_X :
    rationalGraphLocalParameterHom (k := k) R f hker RatFunc.X =
      algebraMap (rationalGraphAlgebra R f) (rationalGraphLocalAlgebra R f hker)
        (rationalGraphPolynomialHom R f Polynomial.X) := by
  rw [rationalGraphLocalParameterHom, ← RatFunc.algebraMap_X, IsLocalization.lift_eq]
  change algebraMap (rationalGraphAlgebra R f) (rationalGraphLocalAlgebra R f hker)
    (rationalGraphPolynomialHom R f (Polynomial.X.map (algebraMap k R))) = _
  rw [Polynomial.map_X]

/-- The graph's local generic parameter has exactly the original
field value f, with no scalar specialization or replacement field. -/
theorem rationalGraphLocalParameterHom_X_value :
    (rationalGraphLocalParameterHom (k := k) R f hker RatFunc.X : F) = f := by
  rw [rationalGraphLocalParameterHom_X]
  exact rationalGraphPolynomialHom_X_value R f

/-- Under the graph specialization the very same generic parameter
remains the rational-function variable in the residue field. -/
theorem rationalGraphLocalParameterHom_X_residue :
    rationalGraphLocalResidueHom R f hker
      (rationalGraphLocalParameterHom (k := k) R f hker RatFunc.X) = RatFunc.X := by
  rw [rationalGraphLocalParameterHom_X, rationalGraphLocalResidueHom_graph_coefficient,
    rationalGraphResidueHom_parameter, RatFunc.algebraMap_X]

end DimensionFourDependence
