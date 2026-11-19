import DimensionFourDependence.ComponentSourceRealizationTransport
import DimensionFourDependence.GenericOutputPoint

/-! # Original outputs on arbitrary coordinate realizations of full generic components -/

namespace DimensionFourDependence

open MvPolynomial

set_option maxHeartbeats 3000000
set_option synthInstance.maxHeartbeats 100000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- The own coordinates of an actual full generic-fiber component
evaluate every original output to its specified full-output constant.
This holds in any coordinate field and for any specified output-field
embedding; no separate ground-field action is required. -/
theorem full_generic_component_original_output_values
    {K B Z : Type*} [Field K] [Field B] [Field Z] [Algebra B Z]
    (H : Fin 4 → MvPolynomial (Fin 4) K)
    (δ : polynomialOutputField H →+* B) (x : Fin 4 → Z) :
    letI : Algebra (polynomialOutputField H) B := δ.toAlgebra
    fiberVanishingIdeal (L := B) x ∈
      (extendCoefficientIdeal B (fiberVanishingIdeal (L := polynomialOutputField H)
        (rationalCoordinate (K := K) (n := 4)))).minimalPrimes →
    ∀ i, MvPolynomial.eval₂
      (((algebraMap B Z).comp δ).comp (algebraMap K (polynomialOutputField H))) x (H i) =
        algebraMap B Z (δ (fullOutputCoordinate (K := K)
          (fun j => algebraMap (MvPolynomial (Fin 4) K)
            (FractionRing (MvPolynomial (Fin 4) K)) (H j)) i)) := by
  let D := polynomialOutputField H
  let S := FractionRing (MvPolynomial (Fin 4) K)
  letI : Algebra D B := δ.toAlgebra
  intro hcomponent
  letI : Algebra D Z := ((algebraMap B Z).comp δ).toAlgebra
  letI : IsScalarTower D B Z := IsScalarTower.of_algebraMap_eq' rfl
  letI : Algebra K Z := ((algebraMap D Z).comp (algebraMap K D)).toAlgebra
  letI : IsScalarTower K D Z := IsScalarTower.of_algebraMap_eq' rfl
  obtain ⟨fD, hf⟩ := full_generic_component_coordinates_construct_source_realization H x hcomponent
  let f : S →ₐ[K] Z := fD.restrictScalars K
  intro i
  have he := comp_aeval_apply (rationalCoordinate (K := K) (n := 4)) f (H i)
  rw [rationalCoordinate_aeval,
    show (fun j => f (rationalCoordinate (K := K) j)) = x from funext hf] at he
  change aeval (R := K) x (H i) = _
  rw [← he]
  exact fD.commutes (fullOutputCoordinate (K := K)
    (fun j => algebraMap (MvPolynomial (Fin 4) K) S (H j)) i)

end DimensionFourDependence
