import DimensionFourDependence.NormalJacobianGaussDimension
import DimensionFourDependence.ScalarExtendedMapHypotheses

/-! # The actual Gauss-image dimension is preserved by coefficient extension

For a nonlinear actual equation, the Gauss dimension plus one is the
rank of the actual polynomial normal Jacobian. Coefficient extension
commutes with that normal and preserves its rational matrix rank.
Cardinal addition by one is injective. The linear-equation case has
Gauss dimension zero over both fields and is handled separately.
-/

namespace DimensionFourDependence

open MvPolynomial

universe u

variable {K F : Type u} [Field K] [CharZero K] [Field F] [Algebra K F]

/-- The actual Gauss-image function-field dimension of the original
rank-three homogeneous polynomial map is unchanged over every extension
of the coefficient field, using the actual extended defining equation. -/
theorem ImageRelationWitness.gauss_image_dimension_scalar_extension
    (H : Fin 4 → MvPolynomial (Fin 4) K) {d : ℕ} (hd : 0 < d) (hH : IsHomogMap H d)
    (hrank : polyRank (jac H) = 3) (I : ImageRelationWitness H) :
    gaussImageDimension (fun i => MvPolynomial.map (algebraMap K F) (H i))
      (I.scalarExtension (E := F) H hrank) = gaussImageDimension H I := by
  let : CharZero F := charZero_of_injective_algebraMap (algebraMap K F).injective
  let HF : Fin 4 → MvPolynomial (Fin 4) F := fun i => MvPolynomial.map (algebraMap K F) (H i)
  let IF : ImageRelationWitness HF := I.scalarExtension (E := F) H hrank
  have hHF : IsHomogMap HF d := isHomogMap_map_coefficients H hH
  change gaussImageDimension HF IF = gaussImageDimension H I
  by_cases he : I.degree = 1
  · have hdegF : IF.degree = 1 := he
    exact (IF.gauss_dimension_zero_of_degree_one HF hHF hdegF).trans
      (I.gauss_dimension_zero_of_degree_one H hH he).symm
  · have hdeg : 1 < I.degree := by have hp := I.degree_pos; omega
    have hdegF : 1 < IF.degree := hdeg
    have hK := I.gauss_add_one_eq_normal_jacobian_rank H hd hH hdeg
    have hF := IF.gauss_add_one_eq_normal_jacobian_rank HF hd hHF hdegF
    have hrN : polyRank (jac (imageRelationNormal HF IF.equation)) =
        polyRank (jac (imageRelationNormal H I.equation)) := by
      change polyRank (jac (imageRelationNormal
        (fun i => MvPolynomial.map (algebraMap K F) (H i))
        (MvPolynomial.map (algebraMap K F) I.equation))) = _
      rw [imageRelationNormal_scalar_extension]
      exact polyRank_jac_map_coefficients (F := F) (imageRelationNormal H I.equation)
    exact Cardinal.add_one_inj.mp
      (hF.trans ((congrArg (fun n : ℕ => (n : Cardinal)) hrN).trans hK.symm))

/-- The rank-three homogeneous map has the same actual Gauss-image
dimension over the algebraic closure of its original coefficient field. -/
theorem ImageRelationWitness.gauss_image_dimension_algebraic_closure
    (H : Fin 4 → MvPolynomial (Fin 4) K) {d : ℕ} (hd : 0 < d) (hH : IsHomogMap H d)
    (hrank : polyRank (jac H) = 3) (I : ImageRelationWitness H) :
    gaussImageDimension (fun i => MvPolynomial.map (algebraMap K (AlgebraicClosure K)) (H i))
      (I.scalarExtension (E := AlgebraicClosure K) H hrank) = gaussImageDimension H I :=
  I.gauss_image_dimension_scalar_extension H hd hH hrank

end DimensionFourDependence
