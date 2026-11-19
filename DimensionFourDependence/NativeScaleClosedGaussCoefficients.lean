import DimensionFourDependence.NativeScaleHomogeneousQuotients
import DimensionFourDependence.ClosedGaussHomogeneousParameter
import DimensionFourDependence.ExtendedOriginalHomogeneousRelations

/-! # The original closed Gauss field has the same independently scaled realization -/

namespace DimensionFourDependence

open MvPolynomial AlgebraicGeometry

set_option maxHeartbeats 3000000
set_option synthInstance.maxHeartbeats 100000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- Rational-function field homomorphisms are determined by their
original coefficient values and their value of the free variable. -/
theorem rational_function_ringHom_ext_C_X
    {k F : Type*} [Field k] [Field F] (f g : RatFunc k →+* F)
    (hC : ∀ c : k, f (RatFunc.C c) = g (RatFunc.C c))
    (hX : f RatFunc.X = g RatFunc.X) : f = g := by
  apply IsLocalization.ringHom_ext (nonZeroDivisors (Polynomial k))
  apply Polynomial.ringHom_ext
  · intro c
    simpa only [RingHom.comp_apply, RatFunc.algebraMap_C] using hC c
  · simpa only [RingHom.comp_apply, RatFunc.algebraMap_X] using hX

universe u

set_option quotPrecheck false

variable {K : Type u} [Field K] [CharZero K]
    (H : Fin 4 → MvPolynomial (Fin 4) K) (I : ImageRelationWitness H)
    (E : Type u) [Field E] [Algebra (closedGaussParameterField H I) E]
    [Algebra.IsAlgebraic (closedGaussParameterField H I) E]
    {d : ℕ} (hH : IsHomogMap H d)
    (e : RatFunc K ≃ₐ[K] closedGaussParameterField H I)

local notation "C₀" => closedGaussParameterField H I
local notation "N" => extendedClosedGaussNormalizationScheme H I E hH e
local notation "w" => extendedClosedGaussNormalizationHyperplaneWeight H I E hH e
local notation "ι" => extendedClosedGaussSourceCoefficientHom H I E
local notation "S₀" => FractionRing (MvPolynomial (Fin 4) K)

local instance nativeScaleClosedGaussCoefficientsIntegral : IsIntegral N :=
  extendedClosedGaussNormalizationScheme_isIntegral H I E hH e
noncomputable local instance nativeScaleClosedGaussCoefficientsExtendedAlgebra : Algebra E (N).functionField :=
  extendedClosedGaussOwnFunctionFieldAlgebra H I E hH e
noncomputable local instance nativeScaleClosedGaussCoefficientsOriginalAlgebra : Algebra K (N).functionField :=
  extendedClosedGaussOriginalSourceAlgebra H I E hH e

/-- A given original equal-degree representation of a closed Gauss
coefficient has exactly that same coefficient value in the native field.
The native relation and its nonzero denominator are derived. -/
theorem native_homogeneous_quotient_realizes_original_closed_coefficient
    (c : C₀) (P Q : MvPolynomial (Fin 4) K) {D : ℕ}
    (hP : P.IsHomogeneous D) (hQ : Q.IsHomogeneous D) (hQ0 : Q ≠ 0)
    (hrep : (c : S₀) = algebraMap _ S₀ P / algebraMap _ S₀ Q) :
    aeval (R := E) (w) (MvPolynomial.map (ι) P) /
      aeval (R := E) (w) (MvPolynomial.map (ι) Q) =
        algebraMap E (N).functionField (algebraMap C₀ E c) := by
  let R := MvPolynomial.map (algebraMap K C₀) P -
    C c * MvPolynomial.map (algebraMap K C₀) Q
  have hR : R.IsHomogeneous D := (hP.map _).sub ((hQ.map _).C_mul c)
  have hQsource : algebraMap (MvPolynomial (Fin 4) K) S₀ Q ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective (MvPolynomial (Fin 4) K) S₀)).mpr hQ0
  have hsource : aeval (R := C₀) (rationalCoordinate (K := K) (n := 4)) R = 0 := by
    simp only [R, map_sub, map_mul, aeval_C, aeval_map_algebra_extension, rationalCoordinate_aeval]
    exact sub_eq_zero.mpr ((eq_div_iff hQsource).mp hrep).symm
  have hn := extendedClosedGauss_original_homogeneous_relation H I E hH e R hR hsource
  simp only [R, map_sub, map_mul, MvPolynomial.map_C, MvPolynomial.map_map, aeval_C] at hn
  change aeval (R := E) (w) (MvPolynomial.map (ι) P) -
    algebraMap E (N).functionField (algebraMap C₀ E c) *
      aeval (R := E) (w) (MvPolynomial.map (ι) Q) = 0 at hn
  have hQnative : aeval (R := E) (w) (MvPolynomial.map (ι) Q) ≠ 0 := by
    intro hz
    exact hQ0 ((native_original_homogeneous_polynomial_zero_iff H I E hH e Q hQ).mp hz)
  exact (div_eq_iff hQnative).mpr (sub_eq_zero.mp hn)

/-- A closed coefficient with an original homogeneous representation
is retained by the actual independently scaled source embedding. -/
theorem nativeIndependentScaleSourceFieldHom_closed_coefficient_of_homogeneous_quotient
    (L : MvPolynomial (Fin 4) E) (hL : aeval (R := E) (w) L ≠ 0)
    (c : C₀) (P Q : MvPolynomial (Fin 4) K) {D : ℕ}
    (hP : P.IsHomogeneous D) (hQ : Q.IsHomogeneous D) (hQ0 : Q ≠ 0)
    (hrep : (c : S₀) = algebraMap _ S₀ P / algebraMap _ S₀ Q) :
    nativeIndependentScaleSourceFieldHom H I E hH e L hL (c : S₀) =
      RatFunc.C (algebraMap E (N).functionField (algebraMap C₀ E c)) := by
  rw [hrep, nativeIndependentScaleSourceFieldHom_homogeneous_quotient H I E hH e L hL P Q hP hQ,
    native_homogeneous_quotient_realizes_original_closed_coefficient H I E hH e c P Q hP hQ hQ0 hrep]

/-- The constructed original homogeneous Gauss parameter is retained
without any choice of an incompatible coefficient realization. -/
theorem nativeIndependentScaleSourceFieldHom_closed_parameter_X
    (L : MvPolynomial (Fin 4) E) (hL : aeval (R := E) (w) L ≠ 0) :
    nativeIndependentScaleSourceFieldHom H I E hH e L hL
      (closedGaussParameterSourceHom H I e RatFunc.X) =
      RatFunc.C (algebraMap E (N).functionField (algebraMap C₀ E (e RatFunc.X))) := by
  obtain ⟨P, Q, D, hD, hP0, hQ0, hP, hQ, hrel, hrep⟩ :=
    actual_closed_gauss_parameter_reduced_homogeneous_source_quotient H hH I e
  exact nativeIndependentScaleSourceFieldHom_closed_coefficient_of_homogeneous_quotient
    H I E hH e L hL (e RatFunc.X) P Q hP hQ hQ0 hrep

/-- The entire original closed Gauss field, not only its parameter,
has exactly the specified original coefficient realization under the
independently scaled source embedding. -/
theorem nativeIndependentScaleSourceFieldHom_closed_coefficient
    (L : MvPolynomial (Fin 4) E) (hL : aeval (R := E) (w) L ≠ 0) (c : C₀) :
    nativeIndependentScaleSourceFieldHom H I E hH e L hL (c : S₀) =
      RatFunc.C (algebraMap E (N).functionField (algebraMap C₀ E c)) := by
  let Φ := nativeIndependentScaleSourceFieldHom H I E hH e L hL
  let f : RatFunc K →+* RatFunc (N).functionField :=
    Φ.toRingHom.comp (closedGaussParameterSourceHom H I e).toRingHom
  let g : RatFunc K →+* RatFunc (N).functionField :=
    ((RatFunc.C.comp (algebraMap E (N).functionField)).comp (algebraMap C₀ E)).comp e.toRingHom
  have hC (b : K) : f (RatFunc.C b) = g (RatFunc.C b) := by
    have hs : closedGaussParameterSourceHom H I e (RatFunc.C b) = algebraMap K S₀ b :=
      (closedGaussParameterSourceHom H I e).commutes b
    change Φ (closedGaussParameterSourceHom H I e (RatFunc.C b)) =
      RatFunc.C (algebraMap E (N).functionField (algebraMap C₀ E (e (RatFunc.C b))))
    rw [hs, nativeIndependentScaleSourceFieldHom_coefficient,
      show e (RatFunc.C b) = algebraMap K C₀ b from e.commutes b]
    rfl
  have hX : f RatFunc.X = g RatFunc.X :=
    nativeIndependentScaleSourceFieldHom_closed_parameter_X H I E hH e L hL
  have he := DFunLike.congr_fun (rational_function_ringHom_ext_C_X f g hC hX) (e.symm c)
  change Φ ((e (e.symm c)) : S₀) =
    RatFunc.C (algebraMap E (N).functionField (algebraMap C₀ E (e (e.symm c)))) at he
  rw [e.apply_symm_apply] at he
  exact he

/-- The actual source embedding and the original closed-coefficient
map form the same scalar tower in the independently scaled native field. -/
theorem nativeIndependentScaleSourceFieldHom_closed_coefficient_scalarTower
    (L : MvPolynomial (Fin 4) E) (hL : aeval (R := E) (w) L ≠ 0) :
    letI : Algebra S₀ (RatFunc (N).functionField) :=
      (nativeIndependentScaleSourceFieldHom H I E hH e L hL).toRingHom.toAlgebra
    letI : Algebra C₀ (RatFunc (N).functionField) :=
      ((RatFunc.C.comp (algebraMap E (N).functionField)).comp (algebraMap C₀ E)).toAlgebra
    letI : SMul C₀ (RatFunc (N).functionField) :=
      (((RatFunc.C.comp (algebraMap E (N).functionField)).comp (algebraMap C₀ E)).toAlgebra).toSMul
    IsScalarTower C₀ S₀ (RatFunc (N).functionField) := by
  letI : Algebra S₀ (RatFunc (N).functionField) :=
    (nativeIndependentScaleSourceFieldHom H I E hH e L hL).toRingHom.toAlgebra
  letI : Algebra C₀ (RatFunc (N).functionField) :=
    ((RatFunc.C.comp (algebraMap E (N).functionField)).comp (algebraMap C₀ E)).toAlgebra
  letI : SMul C₀ (RatFunc (N).functionField) :=
    (((RatFunc.C.comp (algebraMap E (N).functionField)).comp (algebraMap C₀ E)).toAlgebra).toSMul
  apply IsScalarTower.of_algebraMap_eq'
  ext c
  exact (nativeIndependentScaleSourceFieldHom_closed_coefficient H I E hH e L hL c).symm

end DimensionFourDependence
