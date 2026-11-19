import DimensionFourDependence.GenericFiberOutput
import DimensionFourDependence.RadialBoundaryEquations

/-! # Section 3.1: exclusion of the radial infinity direction

The point `(0,H)` over the full generic output field is an actual point
of Mathlib's projective spectrum. If it belongs to the projective closure
of any geometric generic fiber component, homogeneous cross equations
make the primitive map fix the generic image. The checked trace
contradiction forces the image to be linear, hence component dependence.
-/

namespace DimensionFourDependence

open MvPolynomial

attribute [local instance] MvPolynomial.gradedAlgebra

variable {K : Type*} [Field K]

/-- The homogeneous coordinates of the radial generic infinity direction. -/
noncomputable def radialGenericOutputVector
    (H : Fin 4 → MvPolynomial (Fin 4) K) (E : Type*) [Field E]
    [Algebra (polynomialOutputField H) E] : Option (Fin 4) → E :=
  fun j => j.elim 0 (genericOutputValue H E)

theorem radialGenericOutputVector_ne_zero
    (H : Fin 4 → MvPolynomial (Fin 4) K) (hH : H ≠ 0) (E : Type*) [Field E]
    [Algebra (polynomialOutputField H) E] : radialGenericOutputVector H E ≠ 0 := by
  intro hz
  apply genericOutputValue_ne_zero H hH E
  funext i
  exact congrFun hz (some i)

/-- The radial direction as an actual point of projective four-space. -/
noncomputable def radialGenericOutputPoint
    (H : Fin 4 → MvPolynomial (Fin 4) K) (hH : H ≠ 0) (E : Type*) [Field E]
    [Algebra (polynomialOutputField H) E] :
    ProjectiveSpectrum (homogeneousSubmodule (Option (Fin 4)) E) :=
  projectiveCoordinatePoint (radialGenericOutputVector H E)
    (radialGenericOutputVector_ne_zero H hH E)

/-- Its homogenizing coordinate is zero, so it is in the infinity hyperplane. -/
theorem radialGenericOutputPoint_at_infinity
    (H : Fin 4 → MvPolynomial (Fin 4) K) (hH : H ≠ 0) (E : Type*) [Field E]
    [Algebra (polynomialOutputField H) E] :
    radialGenericOutputPoint H hH E ∈ ProjectiveSpectrum.zeroLocus
      (homogeneousSubmodule (Option (Fin 4)) E) {X none} := by
  intro p hp
  rw [Set.mem_singleton_iff] at hp
  subst p
  apply (projectiveCoordinatePoint_mem_homogeneous _ _ (isHomogeneous_X (R := E) none)).mpr
  simp only [aeval_X, radialGenericOutputVector, Option.elim_none]

/-- At a radial boundary point the primitive map satisfies its fixed-image
equations over the original coefficient field. -/
theorem radial_generic_boundary_image_relations
    (H P : Fin 4 → MvPolynomial (Fin 4) K) (hH0 : H ≠ 0)
    (g : MvPolynomial (Fin 4) K) {a : ℕ} (hP : IsHomogMap P a)
    (hHP : H = fun i => g * P i) (E : Type*) [Field E]
    [Algebra (polynomialOutputField H) E] [Algebra K E]
    [IsScalarTower K (polynomialOutputField H) E]
    (Q : Ideal (MvPolynomial (Fin 4) E)) [Q.IsPrime]
    (hQ : Q ∈ (extendCoefficientIdeal E (fiberVanishingIdeal
      (L := polynomialOutputField H) (rationalCoordinate (K := K) (n := 4)))).minimalPrimes)
    (hboundary : radialGenericOutputPoint H hH0 E ∈
      projectiveClosureSet (L := E) (primeQuotientCoordinate Q)) :
    ∀ i j, aeval H (X i * P j - X j * P i) = 0 := by
  let HE := fun i => MvPolynomial.map (algebraMap K E) (H i)
  let PE := fun i => MvPolynomial.map (algebraMap K E) (P i)
  have hPE : IsHomogMap PE a := fun i => (hP i).map (algebraMap K E)
  have hHE : HE = fun i => MvPolynomial.map (algebraMap K E) g * PE i := by
    funext i
    change MvPolynomial.map (algebraMap K E) (H i) = _
    rw [congrFun hHP i, map_mul]
  have hcross := radial_boundary_cross_equations HE PE (MvPolynomial.map (algebraMap K E) g)
    hPE hHE (primeQuotientCoordinate Q) (genericOutputValue H E)
    (genericOutputValue_ne_zero H hH0 E)
    (geometric_component_generic_output_evaluation H E Q hQ)
    (radialGenericOutputVector_ne_zero H hH0 E) hboundary
  intro i j
  apply (genericOutputValue_relations H E _).mp
  simp only [map_sub, map_mul, aeval_X]
  simpa only [PE, aeval_map_coefficients] using hcross i j

variable [CharZero K]

/-- Full radial exclusion of Section 3.1, expressed contrapositively:
the radial generic output can occur at infinity only for a linear image.
All image equations, primitive factors and saturated powers are constructed. -/
theorem dependence_of_radial_geometric_generic_infinity
    (H : Fin 4 → MvPolynomial (Fin 4) K) {d : ℕ} (hd : 0 < d) (hH : IsHomogMap H d)
    (hN : IsNilpotent (jac H)) (hrank : polyRank (jac H) = 3)
    (E : Type*) [Field E] [Algebra (polynomialOutputField H) E]
    [Algebra K E] [IsScalarTower K (polynomialOutputField H) E]
    (Q : Ideal (MvPolynomial (Fin 4) E)) [Q.IsPrime]
    (hQ : Q ∈ (extendCoefficientIdeal E (fiberVanishingIdeal
      (L := polynomialOutputField H) (rationalCoordinate (K := K) (n := 4)))).minimalPrimes)
    (hboundary : radialGenericOutputPoint H (rank_three_polynomial_map_ne_zero H hrank) E ∈
      projectiveClosureSet (L := E) (primeQuotientCoordinate Q)) : ComponentsDependent H := by
  have hH0 := rank_three_polynomial_map_ne_zero H hrank
  obtain ⟨g, P, c, _, _, _, hP, hprim, hHP⟩ := exists_primitive_factorization d H hH hH0
  obtain ⟨W⟩ := exists_image_relation_witness H hd hH hN
  apply primitive_radial_image_forces_dependence H hd hH hN hrank W g P hprim hHP
  intro i j
  apply (W.relation_iff_dvd H hrank _).mp
  exact radial_generic_boundary_image_relations H P hH0 g hP hHP E Q hQ hboundary i j

/-- For a nonlinear image the radial point is absent from the actual
projective closure of every geometric generic affine fiber component. -/
theorem radial_generic_output_not_in_geometric_fiber_closure
    (H : Fin 4 → MvPolynomial (Fin 4) K) {d : ℕ} (hd : 0 < d) (hH : IsHomogMap H d)
    (hN : IsNilpotent (jac H)) (hrank : polyRank (jac H) = 3) (hind : ¬ ComponentsDependent H)
    (E : Type*) [Field E] [Algebra (polynomialOutputField H) E]
    [Algebra K E] [IsScalarTower K (polynomialOutputField H) E]
    (Q : Ideal (MvPolynomial (Fin 4) E)) [Q.IsPrime]
    (hQ : Q ∈ (extendCoefficientIdeal E (fiberVanishingIdeal
      (L := polynomialOutputField H) (rationalCoordinate (K := K) (n := 4)))).minimalPrimes) :
    radialGenericOutputPoint H (rank_three_polynomial_map_ne_zero H hrank) E ∉
      projectiveClosureSet (L := E) (primeQuotientCoordinate Q) := by
  intro hboundary
  exact hind (dependence_of_radial_geometric_generic_infinity H hd hH hN hrank E Q hQ hboundary)

end DimensionFourDependence
