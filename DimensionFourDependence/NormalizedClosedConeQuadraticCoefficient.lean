import DimensionFourDependence.NonlinearClosedConeQuadraticCoefficient
import DimensionFourDependence.ParabolaDirectionNormalization

/-! # Projective direction algebraicity suffices for the actual normalized quadratic coefficient -/

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

/-- Algebraicity of the actual projective direction ratios suffices:
the normalized parabola constructs a nonzero parameter-algebraic
numerator kappa and C/A_j^2 = kappa/R. Neither vector-coordinate
algebraicity nor independence of the fiber direction is assumed. -/
theorem actual_closed_cone_projective_direction_constructs_normalized_quadratic_numerator
    {d : ℕ} (hd : 0 < d) (hH : IsHomogMap H d) (hN : IsNilpotent (jac H))
    (hrank : polyRank (jac H) = 3) (hind : ¬ ComponentsDependent H)
    (hGauss : gaussImageDimension H I = 1)
    (hvertex : rationalImageNormal H I.equation (Fin.last 3) = 0)
    (hsourcevertex : rationalPartial (K := K) (Fin.last 3)
      (closedGaussParameterSourceHom H I e RatFunc.X) ≠ 0)
    (t : F) (htrans : Transcendental E t) (x A V : Fin 3 → E) (w B C R y a b : E)
    (hC : C ≠ 0) (hV0 : V ≠ 0) (j : Fin 3) (hj : A j ≠ 0)
    (hline : ∀ i : Fin 3, (x₀) i.castSucc = algebraMap E F (x i) + algebraMap E F (A i) * t)
    (hparabola : (x₀) (Fin.last 3) = algebraMap E F w + algebraMap E F B * t + algebraMap E F C * t ^ 2)
    (hy : algebraMap S₀ F (algebraMap (MvPolynomial (Fin 4) K) S₀ (H (Fin.last 3))) = algebraMap E F y)
    (hR : R ≠ 0) (hb0 : b ≠ 0)
    (hfirst : ∀ i : Fin 3, algebraMap S₀ F (algebraMap (MvPolynomial (Fin 4) K) S₀ (H i.castSucc)) =
      algebraMap E F (V i) * (algebraMap E F R) ^ d)
    (hlast : algebraMap S₀ F (algebraMap (MvPolynomial (Fin 4) K) S₀ (H (Fin.last 3))) =
      algebraMap E F a * (algebraMap E F R) ^ d + algebraMap E F b * (algebraMap E F R) ^ (d - 1) * (L₀))
    (hV : ∀ i, IsAlgebraic g.fieldRange (V i)) (hA : ∀ i, IsAlgebraic g.fieldRange (A i / A j))
    (ha : IsAlgebraic g.fieldRange a) (hb : IsAlgebraic g.fieldRange b) :
    C / (A j) ^ 2 ≠ 0 ∧ ∃ κ : E, κ ≠ 0 ∧ IsAlgebraic g.fieldRange κ ∧ C / (A j) ^ 2 = κ / R := by
  obtain ⟨htnew, _hAj, hCnew, hxnew, hwnew⟩ :=
    actual_vertex_parabola_normalizes_projected_direction t htrans (x₀) x A w B C hC j hj hline hparabola
  exact actual_closed_nonlinear_fixed_vertex_cone_constructs_quadratic_numerator H I e g hg hd hH hN hrank
    hind hGauss hvertex hsourcevertex (algebraMap E F (A j) * t) htnew x (fun i => A i / A j) V
    w (B / A j) (C / (A j) ^ 2) R y a b hCnew hV0 hxnew hwnew hy hR hb0 hfirst hlast hV hA ha hb

end DimensionFourDependence
