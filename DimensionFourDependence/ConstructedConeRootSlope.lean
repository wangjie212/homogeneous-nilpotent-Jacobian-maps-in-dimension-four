import DimensionFourDependence.VertexFrameConeJacobian
import DimensionFourDependence.ConeRootSlopeIdentity

/-! # The original Jacobian and constructed parameter frame derive (4.9)

Parameter-algebraic directrix and normal coefficients are constant for
the constructed transverse partials. The original derivative chain rule
constructs the full matrix (4.8). Its original nilpotence, rather than an
assumed update identity or zero traces, then constructs the cone slope.
-/

namespace DimensionFourDependence

open MvPolynomial Matrix

set_option maxHeartbeats 5000000
set_option synthInstance.maxHeartbeats 100000
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

variable {K F : Type*} [Field K] [CharZero K] [Field F] [CharZero F] [Algebra K F]

section Frame

variable (D : Fin 4 → Derivation K F F) (p : RatFunc K →ₐ[K] F)

local notation "δ" => transverseParameterPartial D (p RatFunc.X)
local notation "T" => vertexParameterPartial D (p RatFunc.X)

/-- The nilpotent original derivative matrix, actual cone-coordinate
values and the constructed parameter frame derive (4.9). The independent
direction and its directrix derivative decomposition remain explicit. -/
theorem original_derivative_frame_constructs_cone_root_slope
    (x : Fin 4 → F) (hcoord : ∀ i j, D i (x j) = if j = i then 1 else 0)
    (ht : D (Fin.last 3) (p RatFunc.X) ≠ 0)
    (Q : Fin 4 → F) (hN : IsNilpotent (Matrix.of (fun (i j : Fin 4) => D j (Q i))))
    {d : ℕ} (hd : 0 < d) (V A ν : Fin 3 → F) (r f a b L α β : F)
    (hr : r ≠ 0) (hβ : β ≠ 0) (hf : f = r ^ d)
    (hfirst : ∀ i : Fin 3, Q i.castSucc = V i * f)
    (hlast : Q (Fin.last 3) = a * f + b * r ^ (d - 1) * L)
    (hV : ∀ i, IsAlgebraic p.fieldRange (V i))
    (hν : ∀ i, IsAlgebraic p.fieldRange (ν i))
    (ha : IsAlgebraic p.fieldRange a) (hb : IsAlgebraic p.fieldRange b)
    (hL : L = ν ⬝ᵥ (fun i : Fin 3 => x i.castSucc)) (hνV : ν ⬝ᵥ V = 0)
    (hVparameter : ∀ i : Fin 3, T (V i) = α * V i + β * A i)
    (hfV : (fun i => δ i f) ⬝ᵥ V ≠ 0)
    (hfA : (fun i => δ i f) ⬝ᵥ A = 0)
    (hhA : (fun i => δ i (Q (Fin.last 3))) ⬝ᵥ A = 0) :
    (fun i => δ i (x (Fin.last 3))) ⬝ᵥ A = (T a - α * a) / β +
      ((T b - α * ((d : F) - 1) * b / (d : F)) * L + b * T L) / (β * r) := by
  have hfixed (c : F) (hc : IsAlgebraic p.fieldRange c) (i : Fin 3) : δ i c = 0 :=
    transverse_parameter_partial_kills_algebraic_coefficient D p ht c hc i
  have hVfixed (i j : Fin 3) : δ j (V i) = 0 := hfixed _ (hV i) j
  obtain ⟨hZt, hgradient⟩ := vertex_parameter_frame_constructs_graph_differential D x hcoord (p RatFunc.X) ht
  have hJac := vertex_parameter_frame_constructs_cone_jacobian_update D (p RatFunc.X) ht
    Q V A f α β hfirst hVfixed hVparameter
  have hupdate : IsNilpotent (coneFixedParameterJacobian V (fun i => δ i f)
      (fun i => δ i (Q (Fin.last 3))) +
      Matrix.vecMulVec (coneParameterUpdateColumn V A (T f + α * f) β f (T (Q (Fin.last 3))))
        (coneGraphParameterDifferential (fun i => δ i (x (Fin.last 3))) (T (x (Fin.last 3))))) := by
    rw [← hgradient, ← hJac]
    exact hN
  let U := coordinateEuler V δ
  have hUfixed (c : F) (hc : IsAlgebraic p.fieldRange c) : U c = 0 := by
    simp only [U, coordinateEuler_apply, hfixed c hc, mul_zero, Finset.sum_const_zero]
  have hUν (i : Fin 3) : U (ν i) = 0 := hUfixed _ (hν i)
  have hUcoords (i : Fin 3) : U (x i.castSucc) = V i :=
    coordinate_direction_coordinate δ (fun i : Fin 3 => x i.castSucc) V
      (vertex_parameter_derivation_frame_coordinate_values D x hcoord (p RatFunc.X)).2.1 i
  have hUL : U L = 0 := by
    rw [hL, derivation_dotProduct]
    simp only [hUν, hUcoords, dotProduct, zero_mul, Finset.sum_const_zero, zero_add]
    exact hνV
  exact nilpotent_cone_root_constructs_parameter_slope_identity T U hd V A
    (fun i => δ i f) (fun i => δ i (Q (Fin.last 3))) (fun i => δ i (x (Fin.last 3)))
    r f (Q (Fin.last 3)) a b L α β (T (x (Fin.last 3))) hr hβ hZt hf hlast
    (hUfixed a ha) (hUfixed b hb) hUL
    (coordinate_direction_apply_eq_gradient_pairing δ V f)
    (coordinate_direction_apply_eq_gradient_pairing δ V (Q (Fin.last 3))) hfV hfA hhA hupdate

end Frame

section OriginalSource

variable [Algebra (FractionRing (MvPolynomial (Fin 4) K)) F]
    [IsScalarTower K (FractionRing (MvPolynomial (Fin 4) K)) F]
    [Algebra.IsAlgebraic (FractionRing (MvPolynomial (Fin 4) K)) F]

local notation "S₀" => FractionRing (MvPolynomial (Fin 4) K)
local notation "D₀" => algebraicPartial (K := K) F
local notation "x₀" => fun i : Fin 4 => algebraMap S₀ F (rationalCoordinate (K := K) i)

/-- For the original polynomial map in an actual algebraic source
extension, nilpotence supplies (4.9) through the constructed source
frame. No nilpotent update matrix or trace identities are supplied. -/
theorem algebraic_original_cone_root_constructs_graph_slope
    (H : Fin 4 → MvPolynomial (Fin 4) K) (hN : IsNilpotent (jac H))
    (p : RatFunc K →ₐ[K] F) (ht : (D₀) (Fin.last 3) (p RatFunc.X) ≠ 0)
    {d : ℕ} (hd : 0 < d) (V A ν : Fin 3 → F) (r f a b L α β : F)
    (hr : r ≠ 0) (hβ : β ≠ 0) (hf : f = r ^ d)
    (hfirst : ∀ i : Fin 3, algebraMap S₀ F (algebraMap (MvPolynomial (Fin 4) K) S₀ (H i.castSucc)) = V i * f)
    (hlast : algebraMap S₀ F (algebraMap (MvPolynomial (Fin 4) K) S₀ (H (Fin.last 3))) =
      a * f + b * r ^ (d - 1) * L)
    (hV : ∀ i, IsAlgebraic p.fieldRange (V i)) (hν : ∀ i, IsAlgebraic p.fieldRange (ν i))
    (ha : IsAlgebraic p.fieldRange a) (hb : IsAlgebraic p.fieldRange b)
    (hL : L = ν ⬝ᵥ (fun i : Fin 3 => (x₀) i.castSucc)) (hνV : ν ⬝ᵥ V = 0)
    (hVparameter : ∀ i : Fin 3, vertexParameterPartial (D₀) (p RatFunc.X) (V i) = α * V i + β * A i)
    (hfV : (fun i => transverseParameterPartial (D₀) (p RatFunc.X) i f) ⬝ᵥ V ≠ 0)
    (hfA : (fun i => transverseParameterPartial (D₀) (p RatFunc.X) i f) ⬝ᵥ A = 0)
    (hhA : (fun i => transverseParameterPartial (D₀) (p RatFunc.X) i
      (algebraMap S₀ F (algebraMap (MvPolynomial (Fin 4) K) S₀ (H (Fin.last 3))))) ⬝ᵥ A = 0) :
    let T := vertexParameterPartial (D₀) (p RatFunc.X)
    (fun i => transverseParameterPartial (D₀) (p RatFunc.X) i ((x₀) (Fin.last 3))) ⬝ᵥ A =
      (T a - α * a) / β +
        ((T b - α * ((d : F) - 1) * b / (d : F)) * L + b * T L) / (β * r) := by
  exact original_derivative_frame_constructs_cone_root_slope (D₀) p (x₀)
    (algebraicPartial_coordinate F) ht
    (fun i => algebraMap S₀ F (algebraMap (MvPolynomial (Fin 4) K) S₀ (H i)))
    (algebraic_original_source_partials_jacobian_nilpotent H hN) hd V A ν r f a b L α β
    hr hβ hf hfirst hlast hV hν ha hb hL hνV hVparameter hfV hfA hhA

end OriginalSource

end DimensionFourDependence
