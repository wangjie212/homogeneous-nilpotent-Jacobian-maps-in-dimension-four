import DimensionFourDependence.Defs

/-! # Exact polynomial relations specialize wherever the common denominator survives

All polynomial expressions in the ratios live in the localization away
from their common denominator. An injective original-field realization
embeds that localization in the original ambient field. A specialization
with nonzero denominator gives a second localization map. Every original
ratio relation therefore remains a relation after specialization.
-/

namespace DimensionFourDependence

open MvPolynomial

variable {K R F E : Type*} [Field K] [CommRing R] [Algebra K R]
variable [Field F] [Algebra K F] [Field E] [Algebra K E] {n : ℕ}

/-- The actual localization map induced by a realization with nonzero
common ratio denominator. No source fraction-field map is presumed. -/
noncomputable def awayRatioLift (g : R →ₐ[K] F) (x : R) (hx : g x ≠ 0) :
    Localization.Away x →+* F := IsLocalization.Away.lift x (isUnit_iff_ne_zero.mpr hx)

/-- The localization map extends the actual original coefficient realization. -/
theorem awayRatioLift_algebraMap (g : R →ₐ[K] F) (x : R) (hx : g x ≠ 0) (r : R) :
    awayRatioLift g x hx (algebraMap R (Localization.Away x) r) = g r :=
  IsLocalization.Away.lift_eq _ _ _

/-- The chosen inverse of the common denominator maps to its actual
inverse in the target field. -/
theorem awayRatioLift_invSelf (g : R →ₐ[K] F) (x : R) (hx : g x ≠ 0) :
    awayRatioLift g x hx (IsLocalization.Away.invSelf (S := Localization.Away x) x) = (g x)⁻¹ := by
  have he := congrArg (awayRatioLift g x hx)
    (IsLocalization.Away.mul_invSelf (S := Localization.Away x) x)
  rw [map_mul, awayRatioLift_algebraMap, map_one] at he
  exact mul_left_cancel₀ hx (he.trans (mul_inv_cancel₀ hx).symm)

/-- Every localized ratio maps to its actual field-valued ratio. -/
theorem awayRatioLift_ratio (g : R →ₐ[K] F) (x : R) (hx : g x ≠ 0) (r : R) :
    awayRatioLift g x hx (algebraMap R (Localization.Away x) r *
      IsLocalization.Away.invSelf (S := Localization.Away x) x) = g r / g x := by
  rw [map_mul, awayRatioLift_algebraMap, awayRatioLift_invSelf, div_eq_mul_inv]

/-- An injective original realization gives an injective actual map
of the denominator localization into its ambient field. -/
theorem awayRatioLift_injective (g : R →ₐ[K] F) (hg : Function.Injective g)
    (x : R) (hx : g x ≠ 0) : Function.Injective (awayRatioLift g x hx) := by
  apply (IsLocalization.injective_iff_map_algebraMap_eq
    (Submonoid.powers x) (awayRatioLift g x hx)).mpr
  intro a b
  constructor
  · exact congrArg (awayRatioLift g x hx)
  · intro he
    rw [awayRatioLift_algebraMap, awayRatioLift_algebraMap] at he
    exact congrArg (algebraMap R (Localization.Away x)) (hg he)

/-- Evaluation of a polynomial in localized ratios maps to actual
ratio evaluation over the original coefficient field. -/
theorem awayRatioLift_eval_polynomial
    (g : R →ₐ[K] F) (x : R) (hx : g x ≠ 0) (N : Fin n → R)
    (P : MvPolynomial (Fin n) K) :
    awayRatioLift g x hx
      (MvPolynomial.eval₂ ((algebraMap R (Localization.Away x)).comp (algebraMap K R))
        (fun i => algebraMap R (Localization.Away x) (N i) *
          IsLocalization.Away.invSelf (S := Localization.Away x) x) P) =
      aeval (fun i => g (N i) / g x) P := by
  rw [MvPolynomial.hom_eval₂]
  have hc : (awayRatioLift g x hx).comp
      ((algebraMap R (Localization.Away x)).comp (algebraMap K R)) = algebraMap K F := by
    ext c
    change awayRatioLift g x hx
      (algebraMap R (Localization.Away x) (algebraMap K R c)) = algebraMap K F c
    rw [awayRatioLift_algebraMap]
    exact g.commutes c
  have hN : (fun i => awayRatioLift g x hx
      (algebraMap R (Localization.Away x) (N i) * IsLocalization.Away.invSelf (S := Localization.Away x) x)) =
      (fun i => g (N i) / g x) := by
    funext i
    exact awayRatioLift_ratio g x hx (N i)
  rw [hc, hN]
  rfl

/-- Every exact original ratio relation survives an actual
specialization whose common denominator is nonzero. -/
theorem ratio_polynomial_relations_specialize
    (f : R →ₐ[K] F) (hf : Function.Injective f) (g : R →ₐ[K] E)
    (x : R) (hfx : f x ≠ 0) (hgx : g x ≠ 0) (N : Fin n → R)
    (P : MvPolynomial (Fin n) K) (hP : aeval (fun i => f (N i) / f x) P = 0) :
    aeval (fun i => g (N i) / g x) P = 0 := by
  let Q : Localization.Away x :=
    MvPolynomial.eval₂ ((algebraMap R (Localization.Away x)).comp (algebraMap K R))
      (fun i => algebraMap R (Localization.Away x) (N i) *
        IsLocalization.Away.invSelf (S := Localization.Away x) x) P
  have hQ : Q = 0 := by
    apply awayRatioLift_injective f hf x hfx
    rw [map_zero]
    exact (awayRatioLift_eval_polynomial f x hfx N P).trans hP
  have he := congrArg (awayRatioLift g x hgx) hQ
  rw [map_zero] at he
  exact (awayRatioLift_eval_polynomial g x hgx N P).symm.trans he

end DimensionFourDependence
