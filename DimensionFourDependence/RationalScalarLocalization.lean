import DimensionFourDependence.GenericGraphProjectiveBoundary
import Mathlib.RingTheory.Localization.Basic

/-! # A rational scalar extension that retains an actual coefficient specialization -/

namespace DimensionFourDependence

open Polynomial

set_option maxHeartbeats 3000000
set_option synthInstance.maxHeartbeats 100000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable (L A : Type*) [Field L] [CommRing A] [Algebra L A]

/-- Only nonzero polynomials in the new scalar over the original
coefficient field are inverted. Original local coefficients are retained. -/
noncomputable def rationalScalarDenominators : Submonoid (Polynomial A) :=
  (nonZeroDivisors (Polynomial L)).map (Polynomial.mapRingHom (algebraMap L A))

/-- This actual localization permits the same coefficient specialization
before and after adjoining a free rational scalar. -/
abbrev rationalScalarLocalization := Localization (rationalScalarDenominators L A)

/-- The free rational scalar field embeds in the constructed localization. -/
noncomputable def rationalScalarParameterHom : RatFunc L →+* rationalScalarLocalization L A :=
  IsLocalization.lift (M := nonZeroDivisors (Polynomial L)) (S := RatFunc L)
    (g := (algebraMap (Polynomial A) (rationalScalarLocalization L A)).comp
      (Polynomial.mapRingHom (algebraMap L A))) (by
        intro y
        let yA : rationalScalarDenominators L A :=
          ⟨Polynomial.map (algebraMap L A) (y : Polynomial L), by
            change Polynomial.map (algebraMap L A) (y : Polynomial L) ∈
              (nonZeroDivisors (Polynomial L)).map (Polynomial.mapRingHom (algebraMap L A))
            exact ⟨y, y.property, rfl⟩⟩
        exact IsLocalization.map_units (rationalScalarLocalization L A) yA)

/-- Original coefficient elements are constant polynomials followed by
the actual localization map. -/
noncomputable def rationalScalarCoefficientHom : A →+* rationalScalarLocalization L A :=
  (algebraMap (Polynomial A) (rationalScalarLocalization L A)).comp Polynomial.C

variable {G : Type*} [Field G] [Algebra L G]

/-- Any actual coefficient specialization extends to rational functions
in the independent scalar, since its prescribed denominators stay nonzero. -/
noncomputable def rationalScalarSpecialization (φ : A →ₐ[L] G) :
    rationalScalarLocalization L A →+* RatFunc G :=
  IsLocalization.lift (M := rationalScalarDenominators L A)
    (S := rationalScalarLocalization L A)
    (g := (algebraMap (Polynomial G) (RatFunc G)).comp (Polynomial.mapRingHom φ.toRingHom)) (by
      rintro ⟨y, hy⟩
      obtain ⟨P, hP, rfl⟩ := hy
      apply isUnit_iff_ne_zero.mpr
      apply (map_ne_zero_iff _ (IsFractionRing.injective (Polynomial G) (RatFunc G))).mpr
      change Polynomial.map φ.toRingHom (Polynomial.map (algebraMap L A) P) ≠ 0
      rw [Polynomial.map_map]
      have hc : φ.toRingHom.comp (algebraMap L A) = algebraMap L G := by
        ext c
        exact φ.commutes c
      change Polynomial.map (φ.toRingHom.comp (algebraMap L A)) P ≠ 0
      rw [hc]
      exact (map_ne_zero_iff (Polynomial.mapRingHom (algebraMap L G))
        (Polynomial.map_injective (algebraMap L G) (algebraMap L G).injective)).mpr
          (mem_nonZeroDivisors_iff_ne_zero.mp hP))

/-- The specialization keeps every original scalar polynomial value. -/
theorem rationalScalarSpecialization_polynomial (φ : A →ₐ[L] G) (P : Polynomial A) :
    rationalScalarSpecialization L A φ
      (algebraMap (Polynomial A) (rationalScalarLocalization L A) P) =
      algebraMap (Polynomial G) (RatFunc G) (P.map φ.toRingHom) := by
  exact IsLocalization.lift_eq _ P

/-- Original coefficients specialize by exactly the given original map. -/
theorem rationalScalarSpecialization_coefficient (φ : A →ₐ[L] G) (a : A) :
    rationalScalarSpecialization L A φ (rationalScalarCoefficientHom L A a) = RatFunc.C (φ a) := by
  rw [rationalScalarCoefficientHom, RingHom.comp_apply, rationalScalarSpecialization_polynomial,
    Polynomial.map_C, RatFunc.algebraMap_C]
  rfl

/-- The independent scalar remains the free variable after specialization. -/
theorem rationalScalarSpecialization_variable (φ : A →ₐ[L] G) :
    rationalScalarSpecialization L A φ
      (algebraMap (Polynomial A) (rationalScalarLocalization L A) Polynomial.X) = RatFunc.X := by
  rw [rationalScalarSpecialization_polynomial, Polynomial.map_X, RatFunc.algebraMap_X]

/-- An injective original inclusion gives an injective inclusion of
the actual scalar localization into the rationally extended original field. -/
theorem rationalScalarSpecialization_injective (φ : A →ₐ[L] G) (hφ : Function.Injective φ) :
    Function.Injective (rationalScalarSpecialization L A φ) := by
  have hg := (IsFractionRing.injective (Polynomial G) (RatFunc G)).comp
    (Polynomial.map_injective φ.toRingHom hφ)
  unfold rationalScalarSpecialization
  apply (IsLocalization.lift_injective_iff _).mpr
  intro x y
  constructor
  · intro h
    have he := congrArg (rationalScalarSpecialization L A φ) h
    rw [rationalScalarSpecialization_polynomial, rationalScalarSpecialization_polynomial] at he
    change algebraMap (Polynomial G) (RatFunc G) (x.map φ.toRingHom) =
      algebraMap (Polynomial G) (RatFunc G) (y.map φ.toRingHom)
    exact he
  · intro h
    exact congrArg (algebraMap (Polynomial A) (rationalScalarLocalization L A)) (hg h)

/-- Scalar constants in the free field retain their original coefficient
inclusion into the actual localization. -/
theorem rationalScalarParameterHom_C (c : L) :
    rationalScalarParameterHom L A (RatFunc.C c) =
      rationalScalarCoefficientHom L A (algebraMap L A c) := by
  rw [rationalScalarParameterHom, ← RatFunc.algebraMap_C, IsLocalization.lift_eq]
  change algebraMap (Polynomial A) (rationalScalarLocalization L A)
    (Polynomial.map (algebraMap L A) (Polynomial.C c)) = _
  rw [Polynomial.map_C]
  rfl

/-- The new field parameter is represented by the actual polynomial
variable in the localization. -/
theorem rationalScalarParameterHom_X :
    rationalScalarParameterHom L A RatFunc.X =
      algebraMap (Polynomial A) (rationalScalarLocalization L A) Polynomial.X := by
  rw [rationalScalarParameterHom, ← RatFunc.algebraMap_X, IsLocalization.lift_eq]
  change algebraMap (Polynomial A) (rationalScalarLocalization L A)
    (Polynomial.map (algebraMap L A) Polynomial.X) = _
  rw [Polynomial.map_X]

end DimensionFourDependence
