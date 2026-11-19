import DimensionFourDependence.GenericFiberOutputEquations
import DimensionFourDependence.ScalarActionOnFiberPrimes
import DimensionFourDependence.HomogeneousEvaluationScaling
import DimensionFourDependence.ScalarExtensionRank

/-! # The actual homogeneous generic fiber is preserved by its roots of unity -/

namespace DimensionFourDependence

open MvPolynomial

universe u
set_option maxHeartbeats 850000
set_option synthInstance.maxHeartbeats 140000

variable {K E : Type u} [Field K] [Field E] {n : ℕ}
local notation "R₀" => MvPolynomial (Fin n) K
local notation "Rₑ" => MvPolynomial (Fin n) E
local notation "x" => (rationalCoordinate (K := K) (n := n))


/-- Over the chosen geometric constants, the actual generic fiber is
still defined by the original output equations with their extended values. -/
theorem geometric_generic_fiber_ideal_eq_extended_output_equations
    (H : Fin n → R₀) [Algebra (polynomialOutputField H) E] [Algebra K E] [IsScalarTower K (polynomialOutputField H) E] :
    extendCoefficientIdeal E (fiberVanishingIdeal (L := (polynomialOutputField H)) x) =
      Ideal.span (Set.range (fun i => MvPolynomial.map (algebraMap K E) (H i) -
        C (algebraMap (polynomialOutputField H) E (genericFiberOutputScalar H i)))) := by
  rw [generic_fiber_vanishing_ideal_eq_output_equations H]
  unfold extendCoefficientIdeal
  rw [Ideal.map_span, ← Set.range_comp]
  have hcomp : (algebraMap (polynomialOutputField H) E).comp (algebraMap K (polynomialOutputField H)) = algebraMap K E := by
    apply RingHom.ext
    intro a
    exact (IsScalarTower.algebraMap_apply K (polynomialOutputField H) E a).symm
  have hMap (i : Fin n) :
      MvPolynomial.map (algebraMap (polynomialOutputField H) E) (genericFiberOutputEquation H i) =
        MvPolynomial.map (algebraMap K E) (H i) - C (algebraMap (polynomialOutputField H) E (genericFiberOutputScalar H i)) := by
    rw [genericFiberOutputEquation, map_sub, MvPolynomial.map_C, MvPolynomial.map_map, hcomp]
  exact congrArg (fun f : Fin n → Rₑ => Ideal.span (Set.range f)) (funext hMap)

/-- Every root of unity of the actual homogeneous degree preserves the
full generic-fiber relation ideal over the chosen coefficient extension. -/
theorem root_of_unity_preserves_homogeneous_generic_fiber_ideal
    (H : Fin n → R₀) [Algebra (polynomialOutputField H) E] [Algebra K E] [IsScalarTower K (polynomialOutputField H) E]
    {d : ℕ} (hH : IsHomogMap H d) (u : rootsOfUnity d E) :
    (extendCoefficientIdeal E (fiberVanishingIdeal (L := (polynomialOutputField H)) x)).comap
      (polynomialScalarEquiv (u : Eˣ)).toRingHom = extendCoefficientIdeal E (fiberVanishingIdeal (L := (polynomialOutputField H)) x) := by
  rw [geometric_generic_fiber_ideal_eq_extended_output_equations (E := E) H]
  let J : Fin n → Rₑ := fun i => MvPolynomial.map (algebraMap K E) (H i) -
    C (algebraMap (polynomialOutputField H) E (genericFiberOutputScalar H i))
  let S := Ideal.span (Set.range J)
  let e := polynomialScalarEquiv (n := n) (u : Eˣ)
  have hu : ((u : Eˣ) : E) ^ d = 1 := (mem_rootsOfUnity' d u.val).mp u.property
  have hJ (i : Fin n) : e (J i) = J i := by
    let P := MvPolynomial.map (algebraMap K E) (H i)
    have hP := (hH i).map (algebraMap K E)
    have eP : e P = P := by
      change polynomialScalarEquiv (u : Eˣ) P = P
      rw [polynomialScalarEquiv_apply, homogeneous_aeval_scaled_coordinates P hP, ← map_pow, hu,
        map_one, one_mul]
    change e (P - C (algebraMap (polynomialOutputField H) E (genericFiberOutputScalar H i))) = _
    rw [map_sub, eP, show ∀ a : E, e (C a) = C a from e.commutes]
  have he : S.map e.toRingHom = S := by
    change (Ideal.span (Set.range J)).map e.toRingHom = Ideal.span (Set.range J)
    rw [Ideal.map_span, ← Set.range_comp]
    exact congrArg (fun f : Fin n → Rₑ => Ideal.span (Set.range f)) (funext hJ)
  change S.comap e.toRingHom = S
  calc
    S.comap e.toRingHom = (S.map e.toRingHom).comap e.toRingHom :=
      congrArg (Ideal.comap e.toRingHom) he.symm
    _ = S := Ideal.comap_map_of_bijective e.toRingHom e.bijective

/-- The actual root-of-unity action on geometric generic components. -/
@[instance_reducible] noncomputable def homogeneousGenericFiberAction
    (H : Fin n → R₀) [Algebra (polynomialOutputField H) E] [Algebra K E] [IsScalarTower K (polynomialOutputField H) E]
    {d : ℕ} (hH : IsHomogMap H d) :
    MulAction (rootsOfUnity d E) (extendCoefficientIdeal E (fiberVanishingIdeal (L := (polynomialOutputField H)) x)).minimalPrimes :=
  scalarActionOnMinimalPrimes d _ (root_of_unity_preserves_homogeneous_generic_fiber_ideal H hH)

end DimensionFourDependence
