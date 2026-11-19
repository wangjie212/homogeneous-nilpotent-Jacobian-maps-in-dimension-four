import DimensionFourDependence.VertexParameterDerivationFrame
import DimensionFourDependence.ConeParameterJacobianSlope
import DimensionFourDependence.AlgebraicPartial

/-! # The actual source parameter frame constructs the cone Jacobian (4.8)

The original nonzero vertex parameter partial constructs both the graph
differential and the fixed-parameter derivations. The full derivative
chain rule constructs the rank-one-update Jacobian from the actual cone
coordinate values. The original polynomial nilpotence survives algebraic
source extension through its uniquely extended original partials.
-/

namespace DimensionFourDependence

open MvPolynomial Matrix

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 100000

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

/-- The actual nonzero vertex partial constructs the complete graph
parameter differential and proves its inverse vertex derivative nonzero. -/
theorem vertex_parameter_frame_constructs_graph_differential
    (D : Fin 4 → Derivation K F F) (x : Fin 4 → F)
    (hcoord : ∀ i j, D i (x j) = if j = i then 1 else 0)
    (t : F) (ht : D (Fin.last 3) t ≠ 0) :
    vertexParameterPartial D t (x (Fin.last 3)) ≠ 0 ∧
      (fun j => D j t) = coneGraphParameterDifferential
        (fun i => transverseParameterPartial D t i (x (Fin.last 3)))
        (vertexParameterPartial D t (x (Fin.last 3))) := by
  obtain ⟨_hx, _hxx, hZt, hZx⟩ := vertex_parameter_derivation_frame_coordinate_values D x hcoord t
  refine ⟨by rw [hZt]; exact inv_ne_zero ht, ?_⟩
  funext j
  refine Fin.lastCases ?_ (fun i => ?_) j
  · simp only [coneGraphParameterDifferential, Fin.snoc_last, hZt, one_div, inv_inv]
  · simp only [coneGraphParameterDifferential, Fin.snoc_castSucc, hZt, hZx]
    field_simp [ht]

/-- The actual cone-coordinate values and constructed parameter frame
give the exact Jacobian rank-one update (4.8). Neither a graph differential
nor a matrix factorization is assumed. -/
theorem vertex_parameter_frame_constructs_cone_jacobian_update
    (D : Fin 4 → Derivation K F F) (t : F) (ht : D (Fin.last 3) t ≠ 0)
    (Q : Fin 4 → F) (V A : Fin 3 → F) (f α β : F)
    (hfirst : ∀ i : Fin 3, Q i.castSucc = V i * f)
    (hVfixed : ∀ i j : Fin 3, transverseParameterPartial D t j (V i) = 0)
    (hVparameter : ∀ i : Fin 3, vertexParameterPartial D t (V i) = α * V i + β * A i) :
    Matrix.of (fun i j => D j (Q i)) =
      coneFixedParameterJacobian V (fun i => transverseParameterPartial D t i f)
        (fun i => transverseParameterPartial D t i (Q (Fin.last 3))) +
      Matrix.vecMulVec (coneParameterUpdateColumn V A (vertexParameterPartial D t f + α * f) β f
        (vertexParameterPartial D t (Q (Fin.last 3)))) (fun j => D j t) := by
  let δ := transverseParameterPartial D t
  let T := vertexParameterPartial D t
  have htrans (i j : Fin 3) : δ j (Q i.castSucc) = V i * δ j f := by
    rw [hfirst, (δ j).leibniz, hVfixed]
    simp only [smul_eq_mul, mul_zero, add_zero]
  have hparam (i : Fin 3) : T (Q i.castSucc) =
      (T f + α * f) * V i + β * f * A i := by
    rw [hfirst, T.leibniz, hVparameter]
    simp only [smul_eq_mul]
    ring
  have hKtop (i : Fin 3) (j : Fin 4) :
      coneFixedParameterJacobian V (fun i => δ i f) (fun i => δ i (Q (Fin.last 3))) i.castSucc j =
        (Fin.snoc (fun k : Fin 3 => V i * δ k f) (0 : F) : Fin 4 → F) j := by
    fin_cases i <;> fin_cases j <;> rfl
  have hKlast (j : Fin 4) :
      coneFixedParameterJacobian V (fun i => δ i f) (fun i => δ i (Q (Fin.last 3))) (Fin.last 3) j =
        (Fin.snoc (fun k : Fin 3 => δ k (Q (Fin.last 3))) (0 : F) : Fin 4 → F) j := by
    fin_cases j <;> rfl
  apply Matrix.ext
  intro i j
  refine Fin.lastCases ?_ (fun i => ?_) i
  · change D j (Q (Fin.last 3)) = _
    rw [Matrix.add_apply, Matrix.vecMulVec_apply, hKlast]
    simp only [coneParameterUpdateColumn, Fin.snoc_last]
    change D j (Q (Fin.last 3)) = _ + T (Q (Fin.last 3)) * D j t
    exact vertex_parameter_derivation_frame_chain_rule D t ht _ j
  · change D j (Q i.castSucc) = _
    rw [Matrix.add_apply, Matrix.vecMulVec_apply, hKtop]
    simp only [coneParameterUpdateColumn, Fin.snoc_castSucc]
    change D j (Q i.castSucc) = _ + ((T f + α * f) * V i + β * f * A i) * D j t
    have he := vertex_parameter_derivation_frame_chain_rule D t ht (Q i.castSucc) j
    change D j (Q i.castSucc) =
      (Fin.snoc (fun k : Fin 3 => δ k (Q i.castSucc)) (0 : F) : Fin 4 → F) j + T (Q i.castSucc) * D j t at he
    simpa only [htrans, hparam] using he

section OriginalSource

variable [CharZero K]
    [Algebra (FractionRing (MvPolynomial (Fin 4) K)) F]
    [IsScalarTower K (FractionRing (MvPolynomial (Fin 4) K)) F]
    [Algebra.IsAlgebraic (FractionRing (MvPolynomial (Fin 4) K)) F]

local notation "S₀" => FractionRing (MvPolynomial (Fin 4) K)

/-- The actual uniquely extended original partials give precisely
the coefficient extension of the original polynomial Jacobian. -/
theorem algebraic_original_source_partials_polynomial_jacobian
    (H : Fin 4 → MvPolynomial (Fin 4) K) :
    Matrix.of (fun i j => algebraicPartial (K := K) F j
      (algebraMap S₀ F (algebraMap (MvPolynomial (Fin 4) K) S₀ (H i)))) =
      (jac H).map ((algebraMap S₀ F).comp (algebraMap (MvPolynomial (Fin 4) K) S₀)) := by
  apply Matrix.ext
  intro i j
  rw [Matrix.of_apply, algebraicPartial_extends, rationalPartial_polynomial]
  rfl

/-- Nilpotence of the original polynomial Jacobian gives nilpotence
of the actual derivative matrix in every algebraic source extension. -/
theorem algebraic_original_source_partials_jacobian_nilpotent
    (H : Fin 4 → MvPolynomial (Fin 4) K) (hN : IsNilpotent (jac H)) :
    IsNilpotent (Matrix.of (fun (i j : Fin 4) => algebraicPartial (K := K) F j
      (algebraMap S₀ F (algebraMap (MvPolynomial (Fin 4) K) S₀ (H i))))) := by
  rw [algebraic_original_source_partials_polynomial_jacobian]
  exact hN.map ((algebraMap S₀ F).comp (algebraMap (MvPolynomial (Fin 4) K) S₀)).mapMatrix

end OriginalSource

end DimensionFourDependence
