import DimensionFourDependence.ActualFiberSourceFrame
import DimensionFourDependence.ParameterDirectionAlgebraicity

/-! # Actual parabolic fiber equations construct (4.9) and its coefficient kappa/r

The geometric direction and directrix decomposition remain explicit.
All derivative conditions along that direction, including output
constancy and the quadratic acceleration, follow from the actual source
coordinates and their fiber equations.
-/

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

/-- Original nilpotence and actual fiber equations construct the
cone slope and acceleration together. No fixed-direction derivative,
output derivative, root derivative or acceleration is supplied. -/
theorem actual_parabolic_original_cone_constructs_slope_and_acceleration
    (H : Fin 4 → MvPolynomial (Fin 4) K) (hN : IsNilpotent (jac H))
    (hp : ∃ τ : E, p RatFunc.X = algebraMap E F τ)
    (ht : (D₀) (Fin.last 3) (p RatFunc.X) ≠ 0)
    (t : F) (htrans : Transcendental E t) (x A : Fin 3 → E) (w B C R y : E)
    (hline : ∀ i : Fin 3, (x₀) i.castSucc = algebraMap E F (x i) + algebraMap E F (A i) * t)
    (hparabola : (x₀) (Fin.last 3) = algebraMap E F w + algebraMap E F B * t + algebraMap E F C * t ^ 2)
    (hy : algebraMap S₀ F (algebraMap (MvPolynomial (Fin 4) K) S₀ (H (Fin.last 3))) = algebraMap E F y)
    {d : ℕ} (hd : 0 < d) (V ν : Fin 3 → F) (a b L α β : F)
    (hR : R ≠ 0) (hβ : β ≠ 0)
    (hfirst : ∀ i : Fin 3, algebraMap S₀ F (algebraMap (MvPolynomial (Fin 4) K) S₀ (H i.castSucc)) =
      V i * (algebraMap E F R) ^ d)
    (hlast : algebraMap S₀ F (algebraMap (MvPolynomial (Fin 4) K) S₀ (H (Fin.last 3))) =
      a * (algebraMap E F R) ^ d + b * (algebraMap E F R) ^ (d - 1) * L)
    (hV : ∀ i, IsAlgebraic p.fieldRange (V i)) (hν : ∀ i, IsAlgebraic p.fieldRange (ν i))
    (ha : IsAlgebraic p.fieldRange a) (hb : IsAlgebraic p.fieldRange b)
    (hL : L = ν ⬝ᵥ (fun i : Fin 3 => (x₀) i.castSucc)) (hνV : ν ⬝ᵥ V = 0)
    (hVparameter : ∀ i : Fin 3, T (V i) = α * V i + β * algebraMap E F (A i))
    (hfV : (fun i => δ i ((algebraMap E F R) ^ d)) ⬝ᵥ V ≠ 0) :
    ∃ D : Derivation K F F,
      (∀ c : E, D (algebraMap E F c) = 0) ∧ D (p RatFunc.X) = 0 ∧
      (∀ i : Fin 3, D ((x₀) i.castSucc) = algebraMap E F (A i)) ∧
      D ((x₀) (Fin.last 3)) = (T a - α * a) / β +
        ((T b - α * ((d : F) - 1) * b / (d : F)) * L + b * T L) / (β * algebraMap E F R) ∧
      D (D ((x₀) (Fin.last 3))) = 2 * algebraMap E F C := by
  obtain ⟨D, hconst, hDt, hDx, _hframe, _hDw, hacc⟩ :=
    actual_parabolic_source_constructs_transverse_frame_derivation p hp ht t htrans x A w B C hline hparabola
  have hchain (u : F) : D u = (fun i => δ i u) ⬝ᵥ (fun i => algebraMap E F (A i)) :=
    algebraic_source_fixed_parameter_direction_apply (p RatFunc.X) ht D hDt _ hDx u
  have hfA : (fun i => δ i ((algebraMap E F R) ^ d)) ⬝ᵥ (fun i => algebraMap E F (A i)) = 0 := by
    rw [← hchain]
    simp only [Derivation.leibniz_pow, hconst, smul_eq_mul, mul_zero, nsmul_zero]
  have hhA : (fun i => δ i (algebraMap S₀ F
      (algebraMap (MvPolynomial (Fin 4) K) S₀ (H (Fin.last 3))))) ⬝ᵥ (fun i => algebraMap E F (A i)) = 0 := by
    rw [← hchain, hy, hconst]
  have hslope := algebraic_original_cone_root_constructs_graph_slope H hN p ht hd V
    (fun i => algebraMap E F (A i)) ν (algebraMap E F R) ((algebraMap E F R) ^ d) a b L α β
    (by simpa only [map_zero] using (algebraMap E F).injective.ne hR)
    hβ rfl hfirst hlast hV hν ha hb hL hνV hVparameter hfV hfA hhA
  exact ⟨D, hconst, hDt, hDx, (hchain _).trans hslope, hacc⟩

/-- With independent actual normal and fiber directions, the
constructed slope supplies kappa != 0, algebraic over the actual
parameter field, and the actual parabolic coefficient C = kappa/R.
Normal-derivative algebraicity and all fiber derivatives are derived. -/
theorem actual_parabolic_original_cone_constructs_nonzero_quadratic_coefficient
    (H : Fin 4 → MvPolynomial (Fin 4) K) (hN : IsNilpotent (jac H))
    (hp : ∃ τ : E, p RatFunc.X = algebraMap E F τ)
    (ht : (D₀) (Fin.last 3) (p RatFunc.X) ≠ 0)
    (t : F) (htrans : Transcendental E t) (x A : Fin 3 → E) (w B C R y : E)
    (hline : ∀ i : Fin 3, (x₀) i.castSucc = algebraMap E F (x i) + algebraMap E F (A i) * t)
    (hparabola : (x₀) (Fin.last 3) = algebraMap E F w + algebraMap E F B * t + algebraMap E F C * t ^ 2)
    (hy : algebraMap S₀ F (algebraMap (MvPolynomial (Fin 4) K) S₀ (H (Fin.last 3))) = algebraMap E F y)
    {d : ℕ} (hd : 0 < d) (V ν : Fin 3 → F) (a b L α β : F)
    (hR : R ≠ 0) (hb0 : b ≠ 0) (hβ : β ≠ 0)
    (hfirst : ∀ i : Fin 3, algebraMap S₀ F (algebraMap (MvPolynomial (Fin 4) K) S₀ (H i.castSucc)) =
      V i * (algebraMap E F R) ^ d)
    (hlast : algebraMap S₀ F (algebraMap (MvPolynomial (Fin 4) K) S₀ (H (Fin.last 3))) =
      a * (algebraMap E F R) ^ d + b * (algebraMap E F R) ^ (d - 1) * L)
    (hV : ∀ i, IsAlgebraic p.fieldRange (V i)) (hν : ∀ i, IsAlgebraic p.fieldRange (ν i))
    (ha : IsAlgebraic p.fieldRange a) (hb : IsAlgebraic p.fieldRange b)
    (hα : IsAlgebraic p.fieldRange α) (hβalg : IsAlgebraic p.fieldRange β)
    (hL : L = ν ⬝ᵥ (fun i : Fin 3 => (x₀) i.castSucc)) (hνV : ν ⬝ᵥ V = 0)
    (hν₁V : (fun i => T (ν i)) ⬝ᵥ V = 0)
    (hνA : ν ⬝ᵥ (fun i => algebraMap E F (A i)) = 0)
    (hnormal : LinearIndependent F ![ν, fun i => T (ν i)])
    (hdirections : LinearIndependent F ![V, fun i => algebraMap E F (A i)])
    (hVparameter : ∀ i : Fin 3, T (V i) = α * V i + β * algebraMap E F (A i))
    (hfV : (fun i => δ i ((algebraMap E F R) ^ d)) ⬝ᵥ V ≠ 0) :
    ∃ κ : F, κ ≠ 0 ∧ IsAlgebraic p.fieldRange κ ∧ algebraMap E F C = κ / algebraMap E F R := by
  obtain ⟨D, hconst, hDt, hDx, hslope, hacc⟩ :=
    actual_parabolic_original_cone_constructs_slope_and_acceleration p H hN hp ht t htrans x A w B C R y
      hline hparabola hy hd V ν a b L α β hR hβ hfirst hlast hV hν ha hb hL hνV hVparameter hfV
  have hT := (vertex_parameter_derivation_frame_parameter_values (D₀) (p RatFunc.X) ht).1
  have hTx := (vertex_parameter_derivation_frame_coordinate_values (D₀) (x₀)
    (algebraicPartial_coordinate F) (p RatFunc.X)).1
  have hpair := parameter_normal_linear_form_mixed_directional_values p T D hT hDt
    ν (fun i : Fin 3 => (x₀) i.castSucc) (fun i => algebraMap E F (A i)) hν hTx hDx
  have hDL : D L = 0 := by rw [hL, hpair.1, hνA]
  have hDTL : D (T L) = (fun i => T (ν i)) ⬝ᵥ (fun i => algebraMap E F (A i)) := by
    rw [hL]; exact hpair.2
  have hθ := independent_cone_direction_first_normal_pairing_ne_zero ν (fun i => T (ν i)) V
    (fun i => algebraMap E F (A i)) hnormal hdirections hνV hν₁V hνA
  have hAalg := parameter_directrix_decomposition_direction_isAlgebraic p T hT V
    (fun i => algebraMap E F (A i)) α β hβ hV hα hβalg hVparameter
  have hθalg := parameter_normal_derivative_direction_pairing_isAlgebraic p T hT ν
    (fun i => algebraMap E F (A i)) hν hAalg
  exact parameter_cone_quadratic_acceleration_constructs_nonzero_coefficient p T D hT hDt
    (algebraMap E F R) ((x₀) (Fin.last 3)) a b L α β
    ((fun i => T (ν i)) ⬝ᵥ (fun i => algebraMap E F (A i))) (algebraMap E F C)
    (by simpa only [map_zero] using (algebraMap E F).injective.ne hR) hb0 hβ hθ ha hb hα hβalg hθalg
    (hconst R) hDL hDTL hslope hacc

end DimensionFourDependence
