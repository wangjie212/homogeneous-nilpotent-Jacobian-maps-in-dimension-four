import DimensionFourDependence.ActualProportionalConeExclusion
import DimensionFourDependence.ActualClosedConeQuadraticCoefficient

/-! # The actual nonlinear cone fiber constructs its own independent direction and quadratic numerator -/

namespace DimensionFourDependence

open MvPolynomial Matrix

set_option quotPrecheck false
set_option maxHeartbeats 6000000
set_option synthInstance.maxHeartbeats 100000
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

variable {K E F : Type*} [Field K] [CharZero K] [Field E] [Field F] [CharZero F]
    [Algebra K E] [Algebra K F] [Algebra E F] [IsScalarTower K E F]
    [Algebra (FractionRing (MvPolynomial (Fin 4) K)) F]
    [IsScalarTower K (FractionRing (MvPolynomial (Fin 4) K)) F]
    [Algebra.IsAlgebraic (FractionRing (MvPolynomial (Fin 4) K)) F]
    (H : Fin 4 → MvPolynomial (Fin 4) K) (I : ImageRelationWitness H)
    (e : RatFunc K ≃ₐ[K] closedGaussParameterField H I)
    (g : closedGaussParameterField H I →ₐ[K] E)
    (hg : ∀ c : closedGaussParameterField H I, algebraMap E F (g c) =
      algebraMap (FractionRing (MvPolynomial (Fin 4) K)) F
        (c : FractionRing (MvPolynomial (Fin 4) K)))

local notation "S₀" => FractionRing (MvPolynomial (Fin 4) K)
local notation "x₀" => fun i : Fin 4 => algebraMap S₀ F (rationalCoordinate (K := K) i)
local notation "p₀" => (IsScalarTower.toAlgHom K S₀ F).comp (closedGaussParameterSourceHom H I e)
local notation "ν₀" => fun i : Fin 3 => (p₀) (closedGaussParameterNormal H I e i.castSucc)
local notation "L₀" => (ν₀) ⬝ᵥ (fun i : Fin 3 => (x₀) i.castSucc)

include hg

/-- The actual nonlinear closed cone fiber constructs C = kappa/R
with kappa != 0 parameter-algebraic in the same geometric constants.
The projected direction's independence is derived by excluding the
proportional case; normal jets, tangent decomposition, nonzero directrix
derivative and all fiber derivative conditions are also conclusions. -/
theorem actual_closed_nonlinear_fixed_vertex_cone_constructs_quadratic_numerator
    {d : ℕ} (hd : 0 < d) (hH : IsHomogMap H d) (hN : IsNilpotent (jac H))
    (hrank : polyRank (jac H) = 3) (hind : ¬ ComponentsDependent H)
    (hGauss : gaussImageDimension H I = 1)
    (hvertex : rationalImageNormal H I.equation (Fin.last 3) = 0)
    (hsourcevertex : rationalPartial (K := K) (Fin.last 3)
      (closedGaussParameterSourceHom H I e RatFunc.X) ≠ 0)
    (t : F) (htrans : Transcendental E t) (x A V : Fin 3 → E) (w B C R y a b : E)
    (hC : C ≠ 0) (hV0 : V ≠ 0)
    (hline : ∀ i : Fin 3, (x₀) i.castSucc = algebraMap E F (x i) + algebraMap E F (A i) * t)
    (hparabola : (x₀) (Fin.last 3) = algebraMap E F w + algebraMap E F B * t + algebraMap E F C * t ^ 2)
    (hy : algebraMap S₀ F (algebraMap (MvPolynomial (Fin 4) K) S₀ (H (Fin.last 3))) = algebraMap E F y)
    (hR : R ≠ 0) (hb0 : b ≠ 0)
    (hfirst : ∀ i : Fin 3, algebraMap S₀ F (algebraMap (MvPolynomial (Fin 4) K) S₀ (H i.castSucc)) =
      algebraMap E F (V i) * (algebraMap E F R) ^ d)
    (hlast : algebraMap S₀ F (algebraMap (MvPolynomial (Fin 4) K) S₀ (H (Fin.last 3))) =
      algebraMap E F a * (algebraMap E F R) ^ d + algebraMap E F b * (algebraMap E F R) ^ (d - 1) * (L₀))
    (hV : ∀ i, IsAlgebraic g.fieldRange (V i)) (hA : ∀ i, IsAlgebraic g.fieldRange (A i))
    (ha : IsAlgebraic g.fieldRange a) (hb : IsAlgebraic g.fieldRange b) :
    C ≠ 0 ∧ ∃ κ : E, κ ≠ 0 ∧ IsAlgebraic g.fieldRange κ ∧ C = κ / R := by
  obtain ⟨hp, ht⟩ := compatible_closed_parameter_constructs_constant_value_and_nonzero_vertex_partial
    H I e g hg hsourcevertex
  have hfirstScalar (i : Fin 3) : algebraMap S₀ F
      (algebraMap (MvPolynomial (Fin 4) K) S₀ (H i.castSucc)) =
        algebraMap E F (V i) * algebraMap E F (R ^ d) := by rw [map_pow]; exact hfirst i
  have hVA := actual_nonlinear_parabolic_cone_constructs_independent_projected_directions
    H hN hrank (p₀) hp ht t htrans x A V w B C (R ^ d) y hC hV0 hline hparabola hy hfirstScalar
    (fun i => compatible_closed_parameter_coefficient_image_isAlgebraic H I e g hg _ (hV i))
  exact actual_closed_fixed_vertex_cone_constructs_quadratic_numerator H I e g hg hd hH hN hrank hind
    hGauss hvertex hsourcevertex t htrans x A V w B C R y a b hline hparabola hy hR hb0
    hfirst hlast hV hA ha hb hVA

end DimensionFourDependence
