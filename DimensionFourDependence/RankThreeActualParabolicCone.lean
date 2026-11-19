import DimensionFourDependence.ConeDirectrixDerivativeNonzero
import DimensionFourDependence.NormalJetTangentDecomposition
import DimensionFourDependence.ActualParabolicConeSlope
import DimensionFourDependence.GeometricQuadraticRootNormalization

/-! # Actual rank-three parabolic cone fibers construct the full coefficient without supplied slopes -/

namespace DimensionFourDependence

open MvPolynomial Matrix

set_option maxHeartbeats 5000000
set_option synthInstance.maxHeartbeats 100000
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

variable {K E F : Type*} [Field K] [CharZero K] [Field E] [Field F] [CharZero F]
    [Algebra K E] [Algebra K F] [Algebra E F] [IsScalarTower K E F]
    [Algebra (FractionRing (MvPolynomial (Fin 4) K)) F]
    [IsScalarTower K (FractionRing (MvPolynomial (Fin 4) K)) F]
    [Algebra.IsAlgebraic (FractionRing (MvPolynomial (Fin 4) K)) F]

local notation "S₀" => FractionRing (MvPolynomial (Fin 4) K)
local notation "x₀" => fun i : Fin 4 => algebraMap S₀ F (rationalCoordinate (K := K) i)
local notation "D₀" => algebraicPartial (K := K) F

variable (p : RatFunc K →ₐ[K] F)

local notation "T" => vertexParameterPartial (D₀) (p RatFunc.X)
local notation "δ" => transverseParameterPartial (D₀) (p RatFunc.X)

/-- The actual parabolic fiber and original rank three force f_V != 0
whenever its projected direction is independent of the directrix. -/
theorem actual_parabolic_rank_three_cone_directrix_derivative_ne_zero
    (H : Fin 4 → MvPolynomial (Fin 4) K) (hrank : polyRank (jac H) = 3)
    (hp : ∃ τ : E, p RatFunc.X = algebraMap E F τ)
    (ht : (D₀) (Fin.last 3) (p RatFunc.X) ≠ 0)
    (t : F) (htrans : Transcendental E t) (x A : Fin 3 → E) (w B C R y : E)
    (hline : ∀ i : Fin 3, (x₀) i.castSucc = algebraMap E F (x i) + algebraMap E F (A i) * t)
    (hparabola : (x₀) (Fin.last 3) = algebraMap E F w + algebraMap E F B * t + algebraMap E F C * t ^ 2)
    (hy : algebraMap S₀ F (algebraMap (MvPolynomial (Fin 4) K) S₀ (H (Fin.last 3))) = algebraMap E F y)
    {d : ℕ} (hd : 0 < d) (V ν : Fin 3 → F) (a b L : F)
    (hR : R ≠ 0)
    (hfirst : ∀ i : Fin 3, algebraMap S₀ F (algebraMap (MvPolynomial (Fin 4) K) S₀ (H i.castSucc)) =
      V i * (algebraMap E F R) ^ d)
    (hlast : algebraMap S₀ F (algebraMap (MvPolynomial (Fin 4) K) S₀ (H (Fin.last 3))) =
      a * (algebraMap E F R) ^ d + b * (algebraMap E F R) ^ (d - 1) * L)
    (hV : ∀ i, IsAlgebraic p.fieldRange (V i)) (hν : ∀ i, IsAlgebraic p.fieldRange (ν i))
    (ha : IsAlgebraic p.fieldRange a) (hb : IsAlgebraic p.fieldRange b)
    (hL : L = ν ⬝ᵥ (fun i : Fin 3 => (x₀) i.castSucc)) (hνV : ν ⬝ᵥ V = 0)
    (hVA : LinearIndependent F ![V, fun i => algebraMap E F (A i)]) :
    (fun i => δ i ((algebraMap E F R) ^ d)) ⬝ᵥ V ≠ 0 := by
  obtain ⟨D, hconst, hDt, hDx, _hframe, _hDw, _hacc⟩ :=
    actual_parabolic_source_constructs_transverse_frame_derivation p hp ht t htrans x A w B C hline hparabola
  have hDQ (i : Fin 4) : D (algebraMap S₀ F
      (algebraMap (MvPolynomial (Fin 4) K) S₀ (H i))) = 0 := by
    refine Fin.lastCases ?_ (fun i => ?_) i
    · rw [hy, hconst]
    · rw [hfirst, D.leibniz,
        parameter_algebraic_coefficient_direction_constant p D hDt _ (hV i)]
      simp only [Derivation.leibniz_pow, hconst, smul_eq_mul, mul_zero, zero_mul, nsmul_zero, zero_add]
  exact original_rank_three_cone_constructs_nonzero_directrix_derivative H hrank p ht D
    (fun i => algebraMap E F (A i)) V ν hDx hDQ hVA hd (algebraMap E F R)
    ((algebraMap E F R) ^ d) a b L
    (by simpa only [map_zero] using (algebraMap E F).injective.ne hR) rfl hfirst hlast hV hν ha hb hL hνV

/-- Original rank three and nilpotence, actual parabolic fiber
equations, the independent actual normal jets and independent projected
direction construct C = kappa/R inside the actual constants. Nonzero
f_V, alpha,beta, their algebraicity, the derivative decomposition,
all fiber derivatives and the nonzero quadratic coefficient are conclusions. -/
theorem actual_parabolic_rank_three_cone_constructs_constant_quadratic_numerator
    (H : Fin 4 → MvPolynomial (Fin 4) K) (hN : IsNilpotent (jac H))
    (hrank : polyRank (jac H) = 3)
    (hp : ∃ τ : E, p RatFunc.X = algebraMap E F τ)
    (ht : (D₀) (Fin.last 3) (p RatFunc.X) ≠ 0)
    (t : F) (htrans : Transcendental E t) (x A : Fin 3 → E) (w B C R y : E)
    (hline : ∀ i : Fin 3, (x₀) i.castSucc = algebraMap E F (x i) + algebraMap E F (A i) * t)
    (hparabola : (x₀) (Fin.last 3) = algebraMap E F w + algebraMap E F B * t + algebraMap E F C * t ^ 2)
    (hy : algebraMap S₀ F (algebraMap (MvPolynomial (Fin 4) K) S₀ (H (Fin.last 3))) = algebraMap E F y)
    {d : ℕ} (hd : 0 < d) (V ν : Fin 3 → F) (a b L : F)
    (hR : R ≠ 0) (hb0 : b ≠ 0)
    (hfirst : ∀ i : Fin 3, algebraMap S₀ F (algebraMap (MvPolynomial (Fin 4) K) S₀ (H i.castSucc)) =
      V i * (algebraMap E F R) ^ d)
    (hlast : algebraMap S₀ F (algebraMap (MvPolynomial (Fin 4) K) S₀ (H (Fin.last 3))) =
      a * (algebraMap E F R) ^ d + b * (algebraMap E F R) ^ (d - 1) * L)
    (hV : ∀ i, IsAlgebraic p.fieldRange (V i)) (hν : ∀ i, IsAlgebraic p.fieldRange (ν i))
    (ha : IsAlgebraic p.fieldRange a) (hb : IsAlgebraic p.fieldRange b)
    (hA : ∀ i, IsAlgebraic p.fieldRange (algebraMap E F (A i)))
    (hL : L = ν ⬝ᵥ (fun i : Fin 3 => (x₀) i.castSucc)) (hνV : ν ⬝ᵥ V = 0)
    (hν₁V : (fun i => T (ν i)) ⬝ᵥ V = 0)
    (hνA : ν ⬝ᵥ (fun i => algebraMap E F (A i)) = 0)
    (hjet : LinearIndependent F ![ν, (fun i => T (ν i)), (fun i => T (T (ν i)))])
    (hVA : LinearIndependent F ![V, fun i => algebraMap E F (A i)]) :
    C ≠ 0 ∧ ∃ κ : E, κ ≠ 0 ∧ IsAlgebraic p.fieldRange (algebraMap E F κ) ∧ C = κ / R := by
  have hT := (vertex_parameter_derivation_frame_parameter_values (D₀) (p RatFunc.X) ht).1
  obtain ⟨α, β, hβ, hαalg, hβalg, hdecomp⟩ :=
    parameter_normal_jets_construct_algebraic_directrix_decomposition p T hT ν V
      (fun i => algebraMap E F (A i)) hjet hVA hνV hν₁V hνA hV hA
  have hfV := actual_parabolic_rank_three_cone_directrix_derivative_ne_zero p H hrank hp ht t htrans
    x A w B C R y hline hparabola hy hd V ν a b L hR hfirst hlast hV hν ha hb hL hνV hVA
  have hnormal : LinearIndependent F ![ν, fun i => T (ν i)] := by
    have he := hjet.comp (Fin.castSucc : Fin 2 → Fin 3) (Fin.castSucc_injective 2)
    convert he using 1
    funext i
    fin_cases i <;> rfl
  obtain ⟨κ, hκ, hκalg, hC⟩ :=
    actual_parabolic_original_cone_constructs_nonzero_quadratic_coefficient p H hN hp ht t htrans
      x A w B C R y hline hparabola hy hd V ν a b L α β hR hb0 hβ hfirst hlast hV hν ha hb
      hαalg hβalg hL hνV hν₁V hνA hnormal hVA hdecomp hfV
  obtain ⟨hC0, κ₀, hκ₀, hκ₀alg, hC₀, _he⟩ :=
    actual_quadratic_coefficient_numerator_descends_to_constants C R κ hR hκ hκalg hC
  exact ⟨hC0, κ₀, hκ₀, hκ₀alg, hC₀⟩

end DimensionFourDependence
