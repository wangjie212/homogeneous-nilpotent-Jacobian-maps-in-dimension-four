import DimensionFourDependence.ActualVertexPolynomialChart
import DimensionFourDependence.ClosedGaussHomogeneousParameter
import DimensionFourDependence.ImageNormalDerivation

/-! # Vertex dependence of the actual Gauss parameter forces output dependence

A derivation annihilating the original map annihilates its image normal,
its projective normal field and its relatively algebraically closed Gauss
cover. Consequently a genuinely vertex-dependent reduced Gauss parameter
forces an original map coordinate to depend on that vertex. This supplies
the nonconstant polynomial source value for the pole argument.
-/

namespace DimensionFourDependence

open MvPolynomial

set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 100000

variable {K : Type*} [Field K] [CharZero K]
    (H : Fin 4 → MvPolynomial (Fin 4) K) (I : ImageRelationWitness H)

local notation "S₀" => FractionRing (MvPolynomial (Fin 4) K)
local notation "L₀" => transverseSourceField K
local notation "w₀" => rationalCoordinate (K := K) (Fin.last 3)

/-- Every derivation annihilating the original map annihilates its
whole relatively algebraically closed Gauss parameter field. -/
theorem closedGaussParameterField_le_vertical_derivation_constants
    (D : Derivation K S₀ S₀)
    (hDH : ∀ i, D (algebraMap (MvPolynomial (Fin 4) K) S₀ (H i)) = 0) :
    closedGaussParameterField H I ≤ derivationConstants D := by
  let M := projectiveRatioField (K := K) (rationalImageNormal H I.equation) (imageNormalPivot H I)
  have hM : M ≤ derivationConstants D := by
    apply projectiveRatioField_le_derivationConstants_of_weight D _ _ 0
    intro i
    simpa only [zero_mul, rationalImageNormal] using imageRelationNormal_vertical_constant H I.equation D hDH i
  let δ := derivationOverConstantSubfield D M hM
  let : CharZero M := charZero_of_injective_algebraMap (algebraMap K M).injective
  intro x hx
  have ha : IsAlgebraic M x := mem_algebraicClosure_iff.mp hx
  exact derivation_zero_of_isAlgebraic δ x ha

/-- Genuine vertex dependence of the original reduced Gauss parameter
constructs an original map coordinate with nonzero vertex derivative. -/
theorem reduced_vertex_gauss_parameter_constructs_output_vertex_derivative
    (e : RatFunc K ≃ₐ[K] closedGaussParameterField H I)
    (p q : MvPolynomial (Fin 4) K) (hp0 : p ≠ 0) (hq0 : q ≠ 0) (hrel : IsRelPrime p q)
    {a b : ℕ} (hp : p.IsHomogeneous a) (hq : q.IsHomogeneous b)
    (hparameter : closedGaussParameterSourceHom H I e RatFunc.X =
      algebraMap (MvPolynomial (Fin 4) K) S₀ p / algebraMap (MvPolynomial (Fin 4) K) S₀ q)
    (hvertex : 0 < p.degreeOf (Fin.last 3) ∨ 0 < q.degreeOf (Fin.last 3)) :
    ∃ i : Fin 4, rationalPartial (K := K) (Fin.last 3)
      (algebraMap (MvPolynomial (Fin 4) K) S₀ (H i)) ≠ 0 := by
  classical
  by_contra! hzero
  have hC := closedGaussParameterField_le_vertical_derivation_constants H I
    (rationalPartial (K := K) (Fin.last 3)) hzero
  have ht : rationalPartial (K := K) (Fin.last 3)
      (closedGaussParameterSourceHom H I e RatFunc.X) = 0 :=
    hC (e RatFunc.X).property
  apply reduced_vertex_parameter_rational_partial_ne_zero p q hp0 hq0 hrel hp hq (Fin.last 3) hvertex
  rwa [← hparameter]

/-- The original reduced Gauss pencil constructs an actual original
coordinate that is a nonconstant polynomial in the vertex variable
over the actual transverse coordinate field. -/
theorem reduced_vertex_gauss_parameter_constructs_nonconstant_vertex_output
    (e : RatFunc K ≃ₐ[K] closedGaussParameterField H I)
    (p q : MvPolynomial (Fin 4) K) (hp0 : p ≠ 0) (hq0 : q ≠ 0) (hrel : IsRelPrime p q)
    {a b : ℕ} (hp : p.IsHomogeneous a) (hq : q.IsHomogeneous b)
    (hparameter : closedGaussParameterSourceHom H I e RatFunc.X =
      algebraMap (MvPolynomial (Fin 4) K) S₀ p / algebraMap (MvPolynomial (Fin 4) K) S₀ q)
    (hvertex : 0 < p.degreeOf (Fin.last 3) ∨ 0 < q.degreeOf (Fin.last 3)) :
    ∃ i : Fin 4, 0 < (sourceVertexPolynomial K (H i)).natDegree := by
  obtain ⟨i, hi⟩ := reduced_vertex_gauss_parameter_constructs_output_vertex_derivative
    H I e p q hp0 hq0 hrel hp hq hparameter hvertex
  refine ⟨i, ?_⟩
  by_contra hpos
  have hconst := Polynomial.eq_C_of_natDegree_eq_zero (Nat.eq_zero_of_not_pos hpos)
  have hL : L₀ ≤ derivationConstants (rationalPartial (K := K) (Fin.last 3)) := by
    apply IntermediateField.adjoin_le_iff.mpr
    rintro _ ⟨j, rfl⟩
    change rationalPartial (K := K) (Fin.last 3) (rationalCoordinate j.castSucc) = 0
    rw [rationalPartial_coordinate]
    simp only [Fin.castSucc_ne_last, ite_false]
  have hvalue : algebraMap (MvPolynomial (Fin 4) K) S₀ (H i) =
      algebraMap L₀ S₀ ((sourceVertexPolynomial K (H i)).coeff 0) := by
    rw [← sourceVertexPolynomial_value, hconst, Polynomial.aeval_C]
    simp only [Polynomial.coeff_C, ite_true]
  apply hi
  rw [hvalue]
  exact hL ((sourceVertexPolynomial K (H i)).coeff 0).property

end DimensionFourDependence
