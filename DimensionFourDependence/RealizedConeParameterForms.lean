import DimensionFourDependence.ActualConeTernaryExpansion
import DimensionFourDependence.RealizedGaussTernaryDescent

/-! # The actual fixed-vertex cone expression constructs its forms over K(t)

The tangent multiple in (4.7) first constructs the complete ternary
forms on the actual algebraic geometric branch. Their actual values
are the embedded original map entries. Compatible coefficient descent
then constructs their forms over the original rational Gauss parameter,
without a supplied ternary expansion or auxiliary scalar actions.
-/

namespace DimensionFourDependence

open MvPolynomial

set_option quotPrecheck false
set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 100000

universe u

variable {K : Type u} [Field K] [CharZero K]
    (H : Fin 4 → MvPolynomial (Fin 4) K) (I : ImageRelationWitness H)
    (E G : Type u) [Field E] [Field G] [Algebra K E] [Algebra K G] [Algebra E G]

local notation "C₀" => closedGaussParameterField H I
local notation "S₀" => FractionRing (MvPolynomial (Fin 4) K)

/-- The original cone expression and its actual tangent multiple
construct homogeneous forms over K(t) representing the original map.
Their exact entire coefficient-branch forms are retained as well. -/
theorem compatible_realized_cone_expression_constructs_parameter_forms
    (g : C₀ →ₐ[K] E) (f : S₀ →ₐ[K] G)
    (hcomp : ∀ c : C₀, algebraMap E G (g c) = f (c : S₀))
    (F : IntermediateField g.fieldRange E) (hF : Algebra.IsAlgebraic g.fieldRange F)
    (e : RatFunc K ≃ₐ[K] C₀)
    (p q : MvPolynomial (Fin 4) K) (hp0 : p ≠ 0) (hq0 : q ≠ 0) (hrel : IsRelPrime p q)
    {a b : ℕ} (hp : p.IsHomogeneous a) (hq : q.IsHomogeneous b)
    (hparameter : closedGaussParameterSourceHom H I e RatFunc.X =
      algebraMap (MvPolynomial (Fin 4) K) S₀ p / algebraMap (MvPolynomial (Fin 4) K) S₀ q)
    (hvertex : 0 < p.degreeOf (Fin.last 3) ∨ 0 < q.degreeOf (Fin.last 3))
    {d : ℕ} (hd : 0 < d) (τ ν V : Fin 3 → F) (u α β : F) (r : G)
    (hr : r = algebraMap F G u *
      (∑ i : Fin 3, algebraMap F G (τ i) * f (rationalCoordinate (K := K) i.castSucc)))
    (hfirst : ∀ i : Fin 3,
      f (algebraMap (MvPolynomial (Fin 4) K) S₀ (H i.castSucc)) = algebraMap F G (V i) * r ^ d)
    (hlast : f (algebraMap (MvPolynomial (Fin 4) K) S₀ (H (Fin.last 3))) =
      algebraMap F G α * r ^ d + algebraMap F G β * r ^ (d - 1) *
        (∑ i : Fin 3, algebraMap F G (ν i) * f (rationalCoordinate (K := K) i.castSucc))) :
    ∃ Q : Fin 4 → MvPolynomial (Fin 3) (RatFunc K), ∀ i,
      MvPolynomial.map (((algebraMap g.fieldRange F).comp g.equivFieldRange.toRingHom).comp e.toRingHom) (Q i) =
        coneTernaryForms d τ ν V u α β i ∧ (Q i).IsHomogeneous d ∧
      MvPolynomial.eval₂ (closedGaussParameterSourceHom H I e).toRingHom
        (fun j : Fin 3 => rationalCoordinate (K := K) j.castSucc) (Q i) =
          algebraMap (MvPolynomial (Fin 4) K) S₀ (H i) := by
  obtain ⟨hhom, hvalue⟩ := cone_form_tangent_multiple_constructs_ternary_expansion hd τ ν V u α β
    (fun i : Fin 3 => f (rationalCoordinate (K := K) i.castSucc)) r
    (fun i : Fin 4 => f (algebraMap (MvPolynomial (Fin 4) K) S₀ (H i))) hr hfirst hlast
  exact compatible_realized_gauss_ternary_forms_descend_to_parameter H I E G g f hcomp F hF
    e p q hp0 hq0 hrel hp hq hparameter hvertex (coneTernaryForms d τ ν V u α β) hhom hvalue

/-- The actual affine fiber and its homogeneous direction equation
derive the source-point tangent multiple, then construct and descend
the cone coordinate forms to K(t). Neither that source identity nor
any ternary form is supplied. -/
theorem compatible_realized_cone_gradient_constructs_parameter_forms
    (g : C₀ →ₐ[K] E) (f : S₀ →ₐ[K] G)
    (hcomp : ∀ c : C₀, algebraMap E G (g c) = f (c : S₀))
    (F : IntermediateField g.fieldRange E) (hF : Algebra.IsAlgebraic g.fieldRange F)
    (e : RatFunc K ≃ₐ[K] C₀)
    (p q : MvPolynomial (Fin 4) K) (hp0 : p ≠ 0) (hq0 : q ≠ 0) (hrel : IsRelPrime p q)
    {a b : ℕ} (hp : p.IsHomogeneous a) (hq : q.IsHomogeneous b)
    (hparameter : closedGaussParameterSourceHom H I e RatFunc.X =
      algebraMap (MvPolynomial (Fin 4) K) S₀ p / algebraMap (MvPolynomial (Fin 4) K) S₀ q)
    (hvertex : 0 < p.degreeOf (Fin.last 3) ∨ 0 < q.degreeOf (Fin.last 3))
    {d : ℕ} (hd : 0 < d) (A : Fin 3 → F) (Φ : MvPolynomial (Fin 3) K) {δ : ℕ}
    (hΦ : Φ.IsHomogeneous δ) (hzero : aeval A Φ = 0)
    (ν V : Fin 3 → F) (u α β : F) (x : Fin 3 → E) (t : G) (r : E)
    (hx : ∀ i : Fin 3, f (rationalCoordinate (K := K) i.castSucc) =
      algebraMap E G (x i) + algebraMap F G (A i) * t)
    (hr : r = algebraMap F E u *
      (∑ i, aeval (fun k => algebraMap F E (A k)) (pderiv i Φ) * x i))
    (hfirst : ∀ i : Fin 3,
      f (algebraMap (MvPolynomial (Fin 4) K) S₀ (H i.castSucc)) =
        algebraMap F G (V i) * (algebraMap E G r) ^ d)
    (hlast : f (algebraMap (MvPolynomial (Fin 4) K) S₀ (H (Fin.last 3))) =
      algebraMap F G α * (algebraMap E G r) ^ d +
        algebraMap F G β * (algebraMap E G r) ^ (d - 1) *
          (∑ i : Fin 3, algebraMap F G (ν i) * f (rationalCoordinate (K := K) i.castSucc))) :
    ∃ Q : Fin 4 → MvPolynomial (Fin 3) (RatFunc K), ∀ i,
      MvPolynomial.map (((algebraMap g.fieldRange F).comp g.equivFieldRange.toRingHom).comp e.toRingHom) (Q i) =
        coneTernaryForms d (fun j => aeval A (pderiv j Φ)) ν V u α β i ∧ (Q i).IsHomogeneous d ∧
      MvPolynomial.eval₂ (closedGaussParameterSourceHom H I e).toRingHom
        (fun j : Fin 3 => rationalCoordinate (K := K) j.castSucc) (Q i) =
          algebraMap (MvPolynomial (Fin 4) K) S₀ (H i) := by
  let : IsScalarTower K F E := IsScalarTower.of_algebraMap_eq (by intro c; rfl)
  let : IsScalarTower F E G := IsScalarTower.of_algebraMap_eq (by intro c; rfl)
  have he := homogeneous_direction_tangent_multiple_actual_source_value
    A Φ hΦ hzero x t (fun i : Fin 3 => f (rationalCoordinate (K := K) i.castSucc)) hx r u hr
  have hr' : algebraMap E G r = algebraMap F G u *
      (∑ i : Fin 3, algebraMap F G (aeval A (pderiv i Φ)) * f (rationalCoordinate (K := K) i.castSucc)) := by
    simpa only [linearFormPolynomial, map_sum, map_mul, aeval_C, aeval_X] using he
  exact compatible_realized_cone_expression_constructs_parameter_forms H I E G g f hcomp F hF
    e p q hp0 hq0 hrel hp hq hparameter hvertex hd _ ν V u α β _ hr' hfirst hlast

end DimensionFourDependence
