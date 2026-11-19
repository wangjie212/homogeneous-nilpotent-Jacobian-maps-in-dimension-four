import DimensionFourDependence.RealizedConeParameterForms
import DimensionFourDependence.ConeLinearFactorDescent
import DimensionFourDependence.PrimitiveMapDegree

/-! # The actual cone gradient constructs its rational common linear factor

The actual affine fiber constructs the ternary coordinate forms over
K(t). Their whole coefficient-branch identities then recover the common
linear factor over K(t), with scalar factors there. Independence of the
original components supplies a nonzero coordinate; no rational covector
or root-descent assertion is assumed.
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

/-- The original affine cone and tangent data construct both their
ternary forms and their common rational linear factor with scalar
coefficients over the original parameter field. -/
theorem compatible_realized_cone_gradient_constructs_rational_linear_factor
    (hind : ¬ ComponentsDependent H)
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
    ∃ Q : Fin 4 → MvPolynomial (Fin 3) (RatFunc K), (∀ i,
      MvPolynomial.map (((algebraMap g.fieldRange F).comp g.equivFieldRange.toRingHom).comp e.toRingHom) (Q i) =
        coneTernaryForms d (fun j => aeval A (pderiv j Φ)) ν V u α β i ∧ (Q i).IsHomogeneous d ∧
      MvPolynomial.eval₂ (closedGaussParameterSourceHom H I e).toRingHom
        (fun j : Fin 3 => rationalCoordinate (K := K) j.castSucc) (Q i) =
          algebraMap (MvPolynomial (Fin 4) K) S₀ (H i)) ∧
      ∃ ℓ : Fin 3 → RatFunc K, ℓ ≠ 0 ∧ ∃ r : Fin 3 → RatFunc K,
        ∀ i : Fin 3, Q i.castSucc = C (r i) * linearFormPolynomial ℓ ^ d := by
  classical
  obtain ⟨Q, hQ⟩ := compatible_realized_cone_gradient_constructs_parameter_forms
    H I E G g f hcomp F hF e p q hp0 hq0 hrel hp hq hparameter hvertex hd A Φ hΦ hzero
      ν V u α β x t r hx hr hfirst hlast
  let ψ : RatFunc K →+* F :=
    ((algebraMap g.fieldRange F).comp g.equivFieldRange.toRingHom).comp e.toRingHom
  let : Algebra (RatFunc K) F := ψ.toAlgebra
  let : CharZero F := charZero_of_injective_algebraMap (algebraMap (RatFunc K) F).injective
  have hH0 : H 0 ≠ 0 := (linearIndependent_of_componentsIndependent H hind).ne_zero 0
  have hQ0 : Q 0 ≠ 0 := by
    intro hz
    have he := (hQ 0).2.2
    rw [hz, MvPolynomial.eval₂_zero] at he
    apply hH0
    apply IsFractionRing.injective (MvPolynomial (Fin 4) K) S₀
    exact he.symm.trans (map_zero _).symm
  obtain ⟨ℓ, hℓ, c, hc⟩ := cone_ternary_forms_construct_rational_linear_power_factor
    ψ Q hd (fun j => aeval A (pderiv j Φ)) ν V u α β (fun i => (hQ i).1) hQ0
  exact ⟨Q, hQ, ℓ, hℓ, c, hc⟩

end DimensionFourDependence
