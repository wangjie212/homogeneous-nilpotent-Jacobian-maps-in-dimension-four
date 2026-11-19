import DimensionFourDependence.ImageRelationNormal

/-! # Constructing the image relation and its actual output-field normal

This supplies the irreducible homogeneous relation and nonzero normal
used at the beginning of Proposition 2.3. Principality of the entire
image relation ideal and the subsequent projective geometry are separate.
-/

namespace DimensionFourDependence

open MvPolynomial Matrix

variable {K : Type*} [Field K] {n m : ℕ}

/-- The checked algebraic data of an irreducible homogeneous image relation. -/
structure ImageRelationWitness (H : Fin n → MvPolynomial (Fin n) K) where
  equation : MvPolynomial (Fin n) K
  degree : ℕ
  degree_pos : 0 < degree
  homogeneous : equation.IsHomogeneous degree
  irreducible : Irreducible equation
  vanishing : aeval H equation = 0
  normal_ne_zero : imageRelationNormal H equation ≠ 0

/-- The recorded image normal is in the left Jacobian kernel. -/
theorem ImageRelationWitness.left_kernel (H : Fin n → MvPolynomial (Fin n) K)
    (W : ImageRelationWitness H) : imageRelationNormal H W.equation ᵥ* jac H = 0 :=
  imageRelationNormal_left_kernel H W.equation W.vanishing

/-- The normal has the degree required for the homogeneous Gauss map. -/
theorem ImageRelationWitness.normal_homogeneous (H : Fin n → MvPolynomial (Fin n) K)
    {d : ℕ} (hH : IsHomogMap H d) (W : ImageRelationWitness H) :
    IsHomogMap (imageRelationNormal H W.equation) (d * (W.degree - 1)) :=
  imageRelationNormal_homogeneous H hH W.equation W.homogeneous

/-- Nilpotence rules out algebraically independent polynomial outputs. -/
theorem polynomial_outputs_dependent_of_nilpotent [CharZero K]
    (H : Fin 4 → MvPolynomial (Fin 4) K) (hN : IsNilpotent (jac H)) :
    ¬ AlgebraicIndependent K H := by
  intro hi
  let Q : Fin 4 → FractionRing (MvPolynomial (Fin 4) K) :=
    fun i => algebraMap (MvPolynomial (Fin 4) K) _ (H i)
  have hQ : AlgebraicIndependent K Q := hi.map'
    (f := IsScalarTower.toAlgHom K (MvPolynomial (Fin 4) K)
      (FractionRing (MvPolynomial (Fin 4) K))) (IsFractionRing.injective _ _)
  have hr := rationalJacobian_rank_of_square_independent Q hQ
  rw [rationalJacobian_polynomial H] at hr
  change polyRank (jac H) = 4 at hr
  have hle := rank_at_most_three H hN
  omega

/-- An irreducible homogeneous relation with nonzero evaluated gradient
is constructed directly from the original nilpotent homogeneous map. -/
theorem exists_image_relation_witness [CharZero K]
    (H : Fin 4 → MvPolynomial (Fin 4) K) {d : ℕ}
    (hd : 0 < d) (hH : IsHomogMap H d) (hN : IsNilpotent (jac H)) :
    Nonempty (ImageRelationWitness H) := by
  obtain ⟨R, e, hR0, hRh, hR, he, hmin⟩ := exists_minimal_homogeneous_relation
    H hd hH (polynomial_outputs_dependent_of_nilpotent H hN)
  exact ⟨{
    equation := R
    degree := e
    degree_pos := he
    homogeneous := hRh
    irreducible := minimal_homogeneous_relation_irreducible H R hR0 hRh hR hmin
    vanishing := hR
    normal_ne_zero := minimal_relation_normal_ne_zero H R hR0 he hRh hmin
  }⟩

variable {F : Type*} [Field F] [Algebra K F]

/-- Every polynomial in the outputs belongs to their actual generated field. -/
theorem aeval_mem_fullOutputField (H : Fin m → F) (P : MvPolynomial (Fin m) K) :
    aeval H P ∈ fullOutputField (K := K) H := by
  apply IntermediateField.algebra_adjoin_le_adjoin K (Set.range H)
  rw [Algebra.adjoin_range_eq_range_aeval]
  exact ⟨P, rfl⟩

/-- Coercing a polynomial substitution to the rational source field
equals substituting the corresponding rational output coordinates. -/
theorem aeval_polynomial_to_fraction (H : Fin m → MvPolynomial (Fin n) K)
    (P : MvPolynomial (Fin m) K) :
    algebraMap (MvPolynomial (Fin n) K) (FractionRing (MvPolynomial (Fin n) K)) (aeval H P) =
      aeval (fun i => algebraMap (MvPolynomial (Fin n) K)
        (FractionRing (MvPolynomial (Fin n) K)) (H i)) P := by
  let f := IsScalarTower.toAlgHom K (MvPolynomial (Fin n) K) (FractionRing (MvPolynomial (Fin n) K))
  have he : f.comp (aeval H) = aeval (fun i => f (H i)) := by
    apply MvPolynomial.algHom_ext
    intro i
    simp
  exact DFunLike.congr_fun he P

/-- The image normal has entries in `K(H)`, hence constant on the
geometric generic fiber before adjoining any further coefficients. -/
theorem imageRelationNormal_mem_fullOutputField
    (H : Fin n → MvPolynomial (Fin n) K) (R : MvPolynomial (Fin n) K) (i : Fin n) :
    algebraMap (MvPolynomial (Fin n) K) (FractionRing (MvPolynomial (Fin n) K))
      (imageRelationNormal H R i) ∈
    fullOutputField (K := K) (fun i => algebraMap (MvPolynomial (Fin n) K)
      (FractionRing (MvPolynomial (Fin n) K)) (H i)) := by
  change algebraMap _ _ (aeval H (pderiv i R)) ∈ _
  rw [aeval_polynomial_to_fraction]
  exact aeval_mem_fullOutputField _ _

/-- The left-kernel equation remains exact in the source rational function field. -/
theorem imageRelationNormal_rational_left_kernel
    (H : Fin n → MvPolynomial (Fin n) K) (R : MvPolynomial (Fin n) K)
    (hR : aeval H R = 0) :
    (fun i => algebraMap (MvPolynomial (Fin n) K) (FractionRing (MvPolynomial (Fin n) K))
      (imageRelationNormal H R i)) ᵥ*
    (jac H).map (algebraMap (MvPolynomial (Fin n) K) (FractionRing (MvPolynomial (Fin n) K))) = 0 := by
  funext j
  have he := congrArg (algebraMap (MvPolynomial (Fin n) K) (FractionRing (MvPolynomial (Fin n) K)))
    (congrFun (imageRelationNormal_left_kernel H R hR) j)
  simpa only [vecMul, dotProduct, Matrix.map_apply, Pi.zero_apply, map_sum, map_mul, map_zero] using he

/-- The actual image normal kills the right-kernel direction in rank
three, by the nilpotent kernel-image inclusion. -/
theorem ImageRelationWitness.kernel_pairing
    (H : Fin 4 → MvPolynomial (Fin 4) K) (hN : IsNilpotent (jac H))
    (hrank : polyRank (jac H) = 3) (W : ImageRelationWitness H)
    (u : Fin 4 → FractionRing (MvPolynomial (Fin 4) K))
    (hu : (jac H).map (algebraMap (MvPolynomial (Fin 4) K)
      (FractionRing (MvPolynomial (Fin 4) K))) *ᵥ u = 0) :
    (fun i => algebraMap (MvPolynomial (Fin 4) K) (FractionRing (MvPolynomial (Fin 4) K))
      (imageRelationNormal H W.equation i)) ⬝ᵥ u = 0 := by
  exact matrix_nilpotent_kernel_dot_zero _
    (hN.map (algebraMap (MvPolynomial (Fin 4) K) (FractionRing (MvPolynomial (Fin 4) K))).mapMatrix)
    (by norm_num) (by change polyRank (jac H) + 1 = 4; omega) _ _
    (imageRelationNormal_rational_left_kernel H W.equation W.vanishing) hu

end DimensionFourDependence
