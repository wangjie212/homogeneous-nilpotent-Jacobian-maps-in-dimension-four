import DimensionFourDependence.ProjectiveImageDimension
import DimensionFourDependence.ZeroDimensionalGaussImage

/-! # Computing the actual Gauss dimension from the polynomial normal

For a nonlinear actual defining equation, its evaluated homogeneous
normal has positive degree. The actual affine normal field therefore
has one more transcendence degree than the actual Gauss ratio field.
The Jacobian criterion computes that affine degree by the normal's
polynomial Jacobian rank. A linear image equation gives Gauss degree zero.
-/

namespace DimensionFourDependence

open MvPolynomial

universe u

variable {K : Type u} [Field K] [CharZero K]

/-- For an actual nonlinear homogeneous image equation, the actual
Gauss dimension plus one is the rational rank of the polynomial normal's
Jacobian. The normal is the evaluated gradient of the actual equation. -/
theorem ImageRelationWitness.gauss_add_one_eq_normal_jacobian_rank
    (H : Fin 4 → MvPolynomial (Fin 4) K) {d : ℕ} (hd : 0 < d) (hH : IsHomogMap H d)
    (I : ImageRelationWitness H) (hdegree : 1 < I.degree) :
    gaussImageDimension H I + 1 = (polyRank (jac (imageRelationNormal H I.equation)) : Cardinal) := by
  have hn : 0 < d * (I.degree - 1) := Nat.mul_pos hd (by omega)
  have hp : imageRelationNormal H I.equation (imageNormalPivot H I) ≠ 0 := by
    intro hz
    exact imageNormalPivot_ne_zero H I (by simp only [rationalImageNormal, hz, map_zero])
  have he := homogeneous_output_trdeg_eq_projective_add_one (imageRelationNormal H I.equation)
    hn (I.normal_homogeneous H hH) (imageNormalPivot H I) hp
  change Algebra.trdeg K (polynomialOutputField (imageRelationNormal H I.equation)) =
    gaussImageDimension H I + 1 at he
  exact he.symm.trans (polynomialOutputField_trdeg_eq_rank (imageRelationNormal H I.equation))

omit [CharZero K] in
/-- A linear actual image equation has zero-dimensional actual Gauss
ratio field over the original field, without algebraic closedness. -/
theorem ImageRelationWitness.gauss_dimension_zero_of_degree_one
    (H : Fin 4 → MvPolynomial (Fin 4) K) {d : ℕ} (hH : IsHomogMap H d)
    (I : ImageRelationWitness H) (hdegree : I.degree = 1) : gaussImageDimension H I = 0 := by
  have hn : IsHomogMap (imageRelationNormal H I.equation) 0 := by
    simpa only [hdegree, Nat.sub_self, mul_zero] using I.normal_homogeneous H hH
  let ν := rationalImageNormal H I.equation
  let a := imageNormalPivot H I
  let c : Fin 4 → K := fun i => (imageRelationNormal H I.equation i).coeff 0
  have hc (i : Fin 4) : ν i = algebraMap K (FractionRing (MvPolynomial (Fin 4) K)) (c i) := by
    change algebraMap (MvPolynomial (Fin 4) K) (FractionRing (MvPolynomial (Fin 4) K))
      (imageRelationNormal H I.equation i) = _
    rw [eq_C_of_isHomogeneous_zero (hn i)]
    rfl
  have hR : projectiveRatioField (K := K) ν a = ⊥ := by
    apply bot_unique
    apply IntermediateField.adjoin_le_iff.mpr
    rintro _ ⟨i, rfl⟩
    change ν i / ν a ∈ (⊥ : IntermediateField K (FractionRing (MvPolynomial (Fin 4) K)))
    rw [hc i, hc a, ← map_div₀]
    exact (⊥ : IntermediateField K (FractionRing (MvPolynomial (Fin 4) K))).algebraMap_mem (c i / c a)
  change Algebra.trdeg K (projectiveRatioField (K := K) ν a) = 0
  rw [hR]
  exact trdeg_eq_zero

/-- In rank three the actual image equation is a plane equation
exactly when the actual Gauss image has dimension zero. -/
theorem ImageRelationWitness.gauss_dimension_zero_iff_degree_one
    (H : Fin 4 → MvPolynomial (Fin 4) K) {d : ℕ} (hd : 0 < d) (hH : IsHomogMap H d)
    (hrank : polyRank (jac H) = 3) (I : ImageRelationWitness H) :
    gaussImageDimension H I = 0 ↔ I.degree = 1 :=
  ⟨I.degree_one_of_gauss_image_dimension_zero H hd hH hrank,
    I.gauss_dimension_zero_of_degree_one H hH⟩

end DimensionFourDependence
