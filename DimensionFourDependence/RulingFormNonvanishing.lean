import DimensionFourDependence.ExtendedChosenGaussRuling

/-! # Actual native output values detect nonzero ruling-restricted forms -/

namespace DimensionFourDependence

open MvPolynomial Matrix AlgebraicGeometry

section Fields

variable {F T : Type*} [Field F] [Field T] [Algebra F T] {n k : ℕ}

/-- A form which vanishes on the original matrix kernel still
vanishes at every point of its scalar-extended kernel. -/
theorem ruling_form_zero_after_extension
    (A : Matrix (Fin k) (Fin n) F) (c : Fin n → F)
    (hc : rulingFormRestriction (LinearMap.ker A.toLin') c = 0)
    (y : Fin n → T) (hy : A.map (algebraMap F T) *ᵥ y = 0) :
    (fun i => algebraMap F T (c i)) ⬝ᵥ y = 0 := by
  have hlinear : rulingFormRestriction (LinearMap.ker A.toLin') c =
      (0 : F) • rulingFormRestriction (LinearMap.ker A.toLin') 0 +
        (0 : F) • rulingFormRestriction (LinearMap.ker A.toLin') 0 := by
    simpa only [zero_smul, zero_add] using hc
  simpa only [map_zero, zero_mul, zero_add] using
    ruling_form_binary_relation_after_extension A c 0 0 0 0 hlinear y hy

/-- A nonzero value at an actual extended kernel point proves the
original ruling-restricted form nonzero. -/
theorem ruling_form_ne_zero_of_extended_value_ne_zero
    (A : Matrix (Fin k) (Fin n) F) (c : Fin n → F)
    (y : Fin n → T) (hy : A.map (algebraMap F T) *ᵥ y = 0)
    (hc : (fun i => algebraMap F T (c i)) ⬝ᵥ y ≠ 0) :
    rulingFormRestriction (LinearMap.ker A.toLin') c ≠ 0 := by
  intro hz
  exact hc (ruling_form_zero_after_extension A c hz y hy)

end Fields

universe u

set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 100000
set_option quotPrecheck false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

variable {K : Type u} [Field K] [CharZero K]
    (H : Fin 4 → MvPolynomial (Fin 4) K) (I : ImageRelationWitness H)
    (E : Type u) [Field E] [Algebra (closedGaussParameterField H I) E]
    [Algebra.IsAlgebraic (closedGaussParameterField H I) E]
    {d : ℕ} (hH : IsHomogMap H d) (e : RatFunc K ≃ₐ[K] closedGaussParameterField H I)
    (hd : 0 < d) (hind : ¬ ComponentsDependent H) (hGauss : gaussImageDimension H I = 1)

local notation "N" => extendedClosedGaussNormalizationScheme H I E hH e
local notation "w" => extendedClosedGaussNormalizationHyperplaneWeight H I E hH e
local notation "A₀" => extendedClosedGaussChosenRulingMatrix H I E hH hd hind hGauss
local notation "W₀" => LinearMap.ker (A₀).toLin'

local instance rulingFormNonvanishingIntegral : IsIntegral N :=
  extendedClosedGaussNormalizationScheme_isIntegral H I E hH e
noncomputable local instance rulingFormNonvanishingAlgebra : Algebra E (N).functionField :=
  extendedClosedGaussOwnFunctionFieldAlgebra H I E hH e

/-- The original nonzero native output form is a nonzero form on
the actual chosen two-dimensional Gauss ruling. -/
theorem extendedClosedGauss_ruling_form_ne_zero_of_native_output_ne_zero
    (c : Fin 4 → E)
    (hc : aeval (w) (extendedClosedGaussOutputLinearPolynomial H I E c) ≠ 0) :
    rulingFormRestriction (W₀) c ≠ 0 := by
  apply ruling_form_ne_zero_of_extended_value_ne_zero (A₀) c
    (fun i => aeval (w) (MvPolynomial.map (extendedClosedGaussSourceCoefficientHom H I E) (H i)))
    (extendedClosedGauss_native_output_mem_chosen_ruling H I E hH e hd hind hGauss)
  simpa only [dotProduct, ← extendedClosedGaussOutputLinearPolynomial_value H I E hH e c] using hc

end DimensionFourDependence
