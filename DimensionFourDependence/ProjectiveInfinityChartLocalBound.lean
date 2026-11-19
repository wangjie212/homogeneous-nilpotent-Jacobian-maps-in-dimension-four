import DimensionFourDependence.PrimitiveBoundaryImage
import DimensionFourDependence.QuadraticBoundaryChart
import DimensionFourDependence.SimplePolynomialSubschemeLocalBound

/-! # The actual projective closure's infinity-chart ideal has the local length bound

The original homogeneous closure ideal is pulled back to the actual
affine infinity chart b+u w+v z. Its equations vanish at the origin
whenever b is an actual closure point. The original affine quadratic
and cubic equations put both leading boundary equations in this chart
ideal. The constructed local quotient map then gives the bound for
this actual chart quotient localization.
-/

namespace DimensionFourDependence

open MvPolynomial Matrix Module

attribute [local instance] MvPolynomial.gradedAlgebra

section Point

variable {E G kappa sigma : Type*} [Field E] [Field G] [Field kappa]
    [Algebra E G] [Algebra E kappa]

/-- Evaluation at radial parameter one recovers all original coordinate
values from the actual projective-point line map. -/
theorem projectiveFieldPointMap_eval_one (z : sigma → kappa) (P : MvPolynomial sigma E) :
    (projectiveFieldPointMap (E := E) z P).eval 1 = aeval z P := by
  have he : ((Polynomial.aeval (1 : kappa)).restrictScalars E).comp
      (projectiveFieldPointMap (E := E) z) = aeval z := by
    apply MvPolynomial.algHom_ext
    intro i
    simp [projectiveFieldPointMap, gradeHom]
  exact DFunLike.congr_fun he P

/-- Every polynomial of the actual homogeneous closure ideal vanishes
at an actual projective closure point, including inhomogeneous relations. -/
theorem projectiveClosureSet_all_coordinate_equations
    (x : sigma → G) (z : Option sigma → kappa) (hz : z ≠ 0)
    (hpoint : projectiveFieldPoint (E := E) z hz ∈ projectiveClosureSet (L := E) x)
    (P : MvPolynomial (Option sigma) E) (hP : P ∈ projectiveConeIdeal (L := E) x) :
    aeval z P = 0 := by
  have hc : projectiveClosureSet (L := E) x =
      ProjectiveSpectrum.zeroLocus (homogeneousSubmodule (Option sigma) E)
        (projectiveConeIdeal (L := E) x : Set (MvPolynomial (Option sigma) E)) := by
    change closure {projectiveClosureGenericPoint (L := E) x} =
      ProjectiveSpectrum.zeroLocus (homogeneousSubmodule (Option sigma) E)
        ((projectiveClosureGenericPoint (L := E) x).asHomogeneousIdeal : Set _)
    rw [← ProjectiveSpectrum.vanishingIdeal_singleton]
    exact (ProjectiveSpectrum.zeroLocus_vanishingIdeal_eq_closure _ _).symm
  rw [hc] at hpoint
  have he := hpoint hP
  change projectiveFieldPointMap (E := E) z P = 0 at he
  have hv := congrArg (Polynomial.eval (1 : kappa)) he
  rwa [projectiveFieldPointMap_eval_one, Polynomial.eval_zero] at hv

end Point

variable {F G : Type*} [Field F] [Field G] [Algebra F G]

/-- The actual original homogeneous coordinates in the affine infinity chart. -/
noncomputable def projectiveInfinityChartHom (b w z : Fin 3 → F) :
    MvPolynomial (Option (Fin 3)) F →ₐ[F] MvPolynomial (Fin 2) F :=
  aeval (fun j : Option (Fin 3) => j.elim 0 (boundaryAffineChartCoordinate b w z))

/-- The actual homogeneous projective closure ideal in the specified
affine infinity chart, including every original closure relation. -/
noncomputable def projectiveInfinityChartIdeal (x : Fin 3 → G) (b w z : Fin 3 → F) :
    Ideal (MvPolynomial (Fin 2) F) :=
  Ideal.map (projectiveInfinityChartHom b w z).toRingHom (projectiveConeIdeal (L := F) x)

/-- A nonzero original infinity direction gives a nonzero full projective vector. -/
theorem infinity_direction_projective_coordinates_ne_zero (b : Fin 3 → F) (hb : b ≠ 0) :
    (fun j : Option (Fin 3) => j.elim 0 b) ≠ 0 := by
  intro hzero
  apply hb
  funext i
  exact congrFun hzero (some i)

/-- Origin evaluation in the actual chart is the original infinity
point evaluation, for every original homogeneous-ring polynomial. -/
theorem projectiveInfinityChartHom_origin (b w z : Fin 3 → F)
    (P : MvPolynomial (Option (Fin 3)) F) :
    aeval (fun _ : Fin 2 => (0 : F)) (projectiveInfinityChartHom b w z P) =
      aeval (fun j : Option (Fin 3) => j.elim 0 b) P := by
  have he : (aeval (fun _ : Fin 2 => (0 : F))).comp (projectiveInfinityChartHom b w z) =
      aeval (fun j : Option (Fin 3) => j.elim 0 b) := by
    apply MvPolynomial.algHom_ext
    intro j
    cases j <;> simp [projectiveInfinityChartHom, boundaryAffineChartCoordinate]
  exact DFunLike.congr_fun he P

/-- The actual closure point constructs the actual origin prime
of the whole infinity-chart ideal; no point-ideal containment is assumed. -/
theorem projectiveInfinityChartIdeal_origin (x : Fin 3 → G) (b w z : Fin 3 → F) (hb : b ≠ 0)
    (hpoint : projectiveFieldPoint (E := F) (fun j : Option (Fin 3) => j.elim 0 b)
      (infinity_direction_projective_coordinates_ne_zero b hb) ∈ projectiveClosureSet (L := F) x) :
    projectiveInfinityChartIdeal x b w z ≤ RingHom.ker (aeval (fun _ : Fin 2 => (0 : F))).toRingHom := by
  apply Ideal.map_le_iff_le_comap.mpr
  intro P hP
  change aeval (fun _ : Fin 2 => (0 : F)) (projectiveInfinityChartHom b w z P) = 0
  rw [projectiveInfinityChartHom_origin]
  exact projectiveClosureSet_all_coordinate_equations x _ _ hpoint P hP

/-- An original affine equation puts its leading homogeneous part
in the actual infinity-chart ideal of the projective closure. -/
theorem projectiveInfinityChartIdeal_leading_equation
    (x : Fin 3 → G) (b w z : Fin 3 → F) (P : MvPolynomial (Fin 3) F)
    (d : ℕ) (hd : P.totalDegree ≤ d) (hP : aeval x P = 0) :
    aeval (boundaryAffineChartCoordinate b w z) (homogeneousComponent d P) ∈
      projectiveInfinityChartIdeal x b w z := by
  have hhom : projectiveHomogenize P d ∈ projectiveConeIdeal (L := F) x := by
    apply (projectiveConeIdeal_mem_of_isHomogeneous x (projectiveHomogenize_isHomogeneous P d hd)).mpr
    rw [projectiveHomogenize_aeval_chart]
    exact hP
  have hm := Ideal.mem_map_of_mem (projectiveInfinityChartHom b w z).toRingHom hhom
  change aeval (fun j : Option (Fin 3) => j.elim 0 (boundaryAffineChartCoordinate b w z))
    (projectiveHomogenize P d) ∈ projectiveInfinityChartIdeal x b w z at hm
  rwa [projectiveHomogenize_aeval_at_infinity P d hd] at hm

variable [CharZero F]

/-- The original quadratic and cubic fiber equations construct both
leading boundary equations inside the entire actual infinity-chart ideal. -/
theorem projectiveInfinityChartIdeal_original_boundary_equations
    (x : Fin 3 → G) (b w z g v Lambda : Fin 3 → F)
    (B S : Matrix (Fin 3) (Fin 3) F) (T : Fin 3 → Fin 3 → Fin 3 → F) (q k : F)
    (hfactor : cubicFormPolynomial T = linearFormPolynomial Lambda * quadraticFormPolynomial B)
    (hQ : aeval x (quadraticFiberPolynomial g B q) = 0)
    (hC : aeval x (cubicFiberPolynomial v S T k) = 0) :
    aeval (boundaryAffineChartCoordinate b w z) (homogeneousComponent 2 (quadraticFiberPolynomial g B q)) ∈
        projectiveInfinityChartIdeal x b w z ∧
      aeval (boundaryAffineChartCoordinate b w z) (modifiedBoundaryQuadric g Lambda S) ∈
        projectiveInfinityChartIdeal x b w z := by
  have hM : aeval x (modifiedCubicFiberPolynomial g v Lambda S q k) = 0 := by
    rw [modifiedCubicFiberPolynomial_elimination_identity g v Lambda B S T q k hfactor]
    simp only [map_add, map_mul, hQ, hC, mul_zero, zero_add]
  refine ⟨projectiveInfinityChartIdeal_leading_equation x b w z _ 2
    (quadraticFiberPolynomial_totalDegree g B q) hQ, ?_⟩
  have hm := projectiveInfinityChartIdeal_leading_equation x b w z _ 2
    (modifiedCubicFiberPolynomial_totalDegree g v Lambda S q k) hM
  rwa [modifiedBoundaryQuadric_eq_leading_component] at hm

/-- The actual projective closure's infinity-chart quotient localization
inherits the local length bound from its original two fiber equations.
No chart-ideal equation membership or local quotient map is supplied. -/
theorem projective_closure_infinity_chart_origin_local_bound
    (x : Fin 3 → G) (b w z g v Lambda : Fin 3 → F) (hb : b ≠ 0)
    (hpoint : projectiveFieldPoint (E := F) (fun j : Option (Fin 3) => j.elim 0 b)
      (infinity_direction_projective_coordinates_ne_zero b hb) ∈ projectiveClosureSet (L := F) x)
    (B S : Matrix (Fin 3) (Fin 3) F) (T : Fin 3 → Fin 3 → Fin 3 → F) (q k : F)
    (hfactor : cubicFormPolynomial T = linearFormPolynomial Lambda * quadraticFormPolynomial B)
    (hQ : aeval x (quadraticFiberPolynomial g B q) = 0)
    (hC : aeval x (cubicFiberPolynomial v S T k) = 0)
    (scalar : F) (hscalar : scalar ≠ 0)
    (hfirst : aeval (boundaryAffineChartCoordinate b w z)
      (homogeneousComponent 2 (quadraticFiberPolynomial g B q)) = C scalar * X 0 ^ 2)
    (hsecond : aeval (fun _ : Fin 2 => (0 : F))
      (aeval (boundaryAffineChartCoordinate b w z) (modifiedBoundaryQuadric g Lambda S)) = 0)
    (htransverse : aeval (fun _ : Fin 2 => (0 : F)) (pderiv 1
      (aeval (boundaryAffineChartCoordinate b w z) (modifiedBoundaryQuadric g Lambda S))) ≠ 0) :
    ∃ hI : projectiveInfinityChartIdeal x b w z ≤ RingHom.ker (aeval (fun _ : Fin 2 => (0 : F))).toRingHom,
      let R := Localization.AtPrime (zeroPointQuotientPrime (projectiveInfinityChartIdeal x b w z) hI)
      Module.Finite F R ∧ finrank F R ≤ 2 ∧ Module.length R R ≤ 2 := by
  have hI := projectiveInfinityChartIdeal_origin x b w z hb hpoint
  have hmem := projectiveInfinityChartIdeal_original_boundary_equations x b w z g v Lambda B S T q k hfactor hQ hC
  refine ⟨hI, ?_⟩
  exact boundary_equations_containing_ideal_origin_local_bound _ _ scalar hscalar hfirst hsecond htransverse
    (projectiveInfinityChartIdeal x b w z) hI hmem.1 hmem.2

end DimensionFourDependence
