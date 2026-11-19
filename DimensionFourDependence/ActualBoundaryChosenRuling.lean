import DimensionFourDependence.ActualFullBoundaryOriginalRuling
import DimensionFourDependence.ActualRootCharacteristicComparison

/-! # The original full boundary belongs to the same chosen extended Gauss ruling -/

namespace DimensionFourDependence

open MvPolynomial Matrix AlgebraicGeometry
open scoped TensorProduct

attribute [local instance] Algebra.TensorProduct.rightAlgebra coefficientFieldScalarTower

universe u

set_option quotPrecheck false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 100000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {K : Type u} [Field K] [CharZero K]
    (H : Fin 4 → MvPolynomial (Fin 4) K) (hrank : polyRank (jac H) = 3) (I : ImageRelationWitness H)
    (p : Equiv.Perm (Fin 4))
    (hY : AlgebraicIndependent K (fun i : Fin 3 => algebraMap (MvPolynomial (Fin 4) K)
      (FractionRing (MvPolynomial (Fin 4) K)) (H (p i.castSucc))))
    (h : coefficientField (K := K) (fun i : Fin 3 => algebraMap (MvPolynomial (Fin 4) K)
      (FractionRing (MvPolynomial (Fin 4) K)) (H (p i.castSucc))))
    (hh : (h : FractionRing (MvPolynomial (Fin 4) K)) = algebraMap (MvPolynomial (Fin 4) K)
      (FractionRing (MvPolynomial (Fin 4) K)) (H (p 3)))
    (E : Type u) [Field E] [Algebra (closedGaussParameterField H I) E]
    [Algebra.IsAlgebraic (closedGaussParameterField H I) E]
    {d : ℕ} (hd : 0 < d) (hH : IsHomogMap H d)
    (hind : ¬ComponentsDependent H) (hGauss : gaussImageDimension H I = 1)
    (e : RatFunc K ≃ₐ[K] closedGaussParameterField H I)

local notation "S₀" => FractionRing (MvPolynomial (Fin 4) K)
local notation "C₀" => closedGaussParameterField H I
local notation "Y" => fun i : Fin 3 => algebraMap (MvPolynomial (Fin 4) K) S₀ (H (p i.castSucc))
local notation "L" => coefficientField (K := K) (Y)
local notation "T₀" => S₀ ⊗[C₀] E
local notation "xₜ" => extendedClosedGaussSourceTensorCoordinate H I E
local notation "a" => actualClosedGaussCoefficientHom H I p hY h hh
local notation "a₀" => actualClosedGaussNormalCovector H I e (p 3)
local notation "A" => closedGaussCoefficientGraphSlope H I p hY h hh e
local notation "Aₑ" => fun i => algebraMap C₀ E (e ((A) i))
local notation "y₀" => coefficientCoordinate (K := K) (Y)
local notation "n₀" => parametricRulingDenominator (closedGaussCoefficientParameterHom H I p hY h hh e) (A) (y₀)
local notation "cN" => closedGaussCanonicalRootNumerator H I p hY h hh e E
local notation "O" => extendedClosedGaussOutputLinearPolynomial H I E
local notation "A₀" => extendedClosedGaussChosenRulingMatrix H I E hH hd hind hGauss
local notation "L₀" => linearFormPolynomial ((A₀) 0)
local notation "N₀" => extendedClosedGaussNormalizationScheme H I E hH e
local notation "w" => extendedClosedGaussNormalizationHyperplaneWeight H I E hH e

local instance actualBoundaryChosenRulingIntegral : IsIntegral N₀ :=
  extendedClosedGaussNormalizationScheme_isIntegral H I E hH e
noncomputable local instance actualBoundaryChosenRulingAlgebra : Algebra E (N₀).functionField :=
  extendedClosedGaussOwnFunctionFieldAlgebra H I E hH e

variable (R : Type u) [Field R]
    [Algebra (coefficientField (K := K) (fun i : Fin 3 => algebraMap (MvPolynomial (Fin 4) K)
      (FractionRing (MvPolynomial (Fin 4) K)) (H (p i.castSucc)))) R] [Algebra E R]

include hrank

/-- Original Gauss coefficients keep their actual source values
under the specified compatible closed-cover and graph embeddings. -/
theorem original_gauss_coefficient_maps_eq_of_compatible_closed_cover
    (hcompat :
      letI : Algebra C₀ R := ((algebraMap (L) R).comp (a).toRingHom).toAlgebra
      IsScalarTower C₀ E R)
    (t : projectiveRatioField (K := K) (rationalImageNormal H I.equation) (imageNormalPivot H I)) :
    algebraMap E R (algebraMap C₀ E (algebraMap
      (projectiveRatioField (K := K) (rationalImageNormal H I.equation) (imageNormalPivot H I)) C₀ t)) =
      algebraMap (L) R (actualChartGaussFieldHom H hrank p hY I t) := by
  letI : Algebra C₀ R := ((algebraMap (L) R).comp (a).toRingHom).toAlgebra
  letI : IsScalarTower C₀ E R := hcompat
  rw [← IsScalarTower.algebraMap_apply C₀ E R]
  change algebraMap (L) R ((a) (algebraMap
    (projectiveRatioField (K := K) (rationalImageNormal H I.equation) (imageNormalPivot H I)) C₀ t)) = _
  congr 1

/-- Both original invariant equations put every actual full-fiber
boundary into the same chosen native ruling after its specified
coefficient extension. Ruling membership is derived from the actual
original closure, with all coefficient maps retained. -/
theorem actual_full_boundary_mem_same_chosen_extended_ruling
    (hcompat :
      letI : Algebra C₀ R := ((algebraMap (L) R).comp (a).toRingHom).toAlgebra
      IsScalarTower C₀ E R)
    (c q : L) (hc : (c : S₀) = firstFiberInvariantInChart p (Y) hY h)
    (hq : (q : S₀) = secondFiberInvariant p (Y) hY h c)
    (z : Option (Fin 4) → R) (hz : z ≠ 0)
    (hpoint : projectiveFieldPoint (E := L) z hz ∈
      projectiveClosureSet («L» := L) (rationalCoordinate (K := K) (n := 4)))
    (hz0 : z none = 0) :
    (A₀).map (algebraMap E R) *ᵥ (fun i => z (some i)) = 0 := by
  let e₀ := actualGaussRulingParameterChoice H I hH hd hind hGauss
  have hmatrix : (A₀).map (algebraMap E R) = (actualGaussRulingMatrix H I e₀).map
      ((algebraMap (L) R).comp (actualChartGaussFieldHom H hrank p hY I).toRingHom) := by
    ext j i
    exact original_gauss_coefficient_maps_eq_of_compatible_closed_cover
      H hrank I p hY h hh E R hcompat (actualGaussRulingMatrix H I e₀ j i)
  rw [hmatrix]
  exact actual_full_fiber_boundary_mem_original_gauss_ruling H hrank p hY I e₀ h hh hd hH hGauss
    c q hc hq R z hz hpoint hz0

end DimensionFourDependence
