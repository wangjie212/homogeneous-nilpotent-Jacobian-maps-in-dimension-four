import DimensionFourDependence.AlgebraicSourceDerivationChain
import DimensionFourDependence.MatrixKernelDescent

/-! # Rank three forbids independent projected output-constant directions -/

namespace DimensionFourDependence

open MvPolynomial Matrix Module

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 100000
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

/-- Two vectors in the kernel of a rank-three four-by-four matrix
cannot have independent first three coordinate projections. -/
theorem rank_three_matrix_projected_kernel_pair_not_independent
    {F : Type*} [Field F] (N : Matrix (Fin 4) (Fin 4) F) (hrank : N.rank = 3)
    (u v : Fin 4 → F) (hu : N *ᵥ u = 0) (hv : N *ᵥ v = 0) :
    ¬ LinearIndependent F ![(fun i : Fin 3 => u i.castSucc), (fun i : Fin 3 => v i.castSucc)] := by
  intro hLI
  have hup : (fun i : Fin 3 => u i.castSucc) ≠ 0 := by simpa using hLI.ne_zero (0 : Fin 2)
  have hu0 : u ≠ 0 := by
    intro hz
    apply hup
    funext i
    simpa only [hz, Pi.zero_apply]
  let uker : LinearMap.ker N.toLin' := ⟨u, hu⟩
  have huneq : uker ≠ 0 := fun he => hu0 (congrArg Subtype.val he)
  obtain ⟨r, hr⟩ := (finrank_eq_one_iff_of_nonzero' uker huneq).mp
    (rank_three_matrix_kernel_finrank N hrank) ⟨v, hv⟩
  have he : r • u = v := congrArg Subtype.val hr
  apply (LinearIndependent.pair_iff' hup).mp hLI r
  funext i
  exact congrFun he i.castSucc

variable {K F : Type*} [Field K] [CharZero K] [Field F] [Algebra K F]
    [Algebra (FractionRing (MvPolynomial (Fin 4) K)) F]
    [IsScalarTower K (FractionRing (MvPolynomial (Fin 4) K)) F]
    [Algebra.IsAlgebraic (FractionRing (MvPolynomial (Fin 4) K)) F]

local notation "S₀" => FractionRing (MvPolynomial (Fin 4) K)
local notation "x₀" => fun i : Fin 4 => algebraMap S₀ F (rationalCoordinate (K := K) i)
local notation "D₀" => algebraicPartial (K := K) F

/-- The original rank-three Jacobian keeps its rank in the actual
algebraic source extension and its constructed coordinate partials. -/
theorem algebraic_original_source_partials_jacobian_rank
    (H : Fin 4 → MvPolynomial (Fin 4) K) (hrank : polyRank (jac H) = 3) :
    (Matrix.of (fun i j : Fin 4 => (D₀) j
      (algebraMap S₀ F (algebraMap (MvPolynomial (Fin 4) K) S₀ (H i))))).rank = 3 := by
  rw [algebraic_original_source_partials_polynomial_jacobian]
  change (((jac H).map (algebraMap (MvPolynomial (Fin 4) K) S₀)).map (algebraMap S₀ F)).rank = 3
  rw [matrix_rank_field_map]
  exact hrank

/-- Every derivation killing the original outputs gives an actual
right-kernel vector through its original coordinate values. -/
theorem algebraic_source_output_constant_derivation_coordinate_kernel
    (H : Fin 4 → MvPolynomial (Fin 4) K) (D : Derivation K F F)
    (hD : ∀ i : Fin 4, D (algebraMap S₀ F
      (algebraMap (MvPolynomial (Fin 4) K) S₀ (H i))) = 0) :
    Matrix.of (fun i j : Fin 4 => (D₀) j
      (algebraMap S₀ F (algebraMap (MvPolynomial (Fin 4) K) S₀ (H i)))) *ᵥ
        (fun i => D ((x₀) i)) = 0 := by
  funext i
  have he := algebraic_source_derivation_coordinate_chain_rule D
    (algebraMap S₀ F (algebraMap (MvPolynomial (Fin 4) K) S₀ (H i)))
  rw [hD] at he
  simpa only [Matrix.mulVec, dotProduct, Matrix.of_apply, Pi.zero_apply, mul_comm] using he.symm

/-- Rank three prevents two actual output-constant derivations from
having independent projected source-coordinate directions. -/
theorem algebraic_source_output_constant_derivations_projected_pair_not_independent
    (H : Fin 4 → MvPolynomial (Fin 4) K) (hrank : polyRank (jac H) = 3)
    (D U : Derivation K F F)
    (hD : ∀ i : Fin 4, D (algebraMap S₀ F (algebraMap (MvPolynomial (Fin 4) K) S₀ (H i))) = 0)
    (hU : ∀ i : Fin 4, U (algebraMap S₀ F (algebraMap (MvPolynomial (Fin 4) K) S₀ (H i))) = 0) :
    ¬ LinearIndependent F ![(fun i : Fin 3 => D ((x₀) i.castSucc)),
      (fun i : Fin 3 => U ((x₀) i.castSucc))] :=
  rank_three_matrix_projected_kernel_pair_not_independent _
    (algebraic_original_source_partials_jacobian_rank H hrank) _ _
    (algebraic_source_output_constant_derivation_coordinate_kernel H D hD)
    (algebraic_source_output_constant_derivation_coordinate_kernel H U hU)

end DimensionFourDependence
