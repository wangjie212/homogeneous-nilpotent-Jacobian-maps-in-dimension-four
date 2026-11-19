import DimensionFourDependence.ProjectiveInfinityChartLocalBound

/-! # Actual infinity charts over a coefficient extension

The original fiber and the extension-valued boundary need not live in
one common field. Pull the original homogeneous closure ideal directly
to the extension-valued chart. This is also the chart image of its
coefficient-extended ideal. Original equations and actual closure
membership still construct the full chart ideal's local bound.
-/

namespace DimensionFourDependence

open MvPolynomial Matrix Module

attribute [local instance] MvPolynomial.gradedAlgebra

variable {E F G : Type*} [Field E] [Field F] [Field G] [Algebra E F] [Algebra E G]

/-- Coefficient extension before evaluation has the same actual
value as evaluation over the original coefficient field. -/
theorem aeval_coefficient_extension
    {A sigma : Type*} [CommRing A] [Algebra F A] [Algebra E A] [IsScalarTower E F A]
    (v : sigma → A) (P : MvPolynomial sigma E) :
    aeval v (MvPolynomial.map (algebraMap E F) P) = (aeval v : MvPolynomial sigma E →ₐ[E] A) P := by
  induction P using MvPolynomial.induction_on with
  | C a =>
    simp only [MvPolynomial.map_C, aeval_C]
    exact (IsScalarTower.algebraMap_apply E F A a).symm
  | add P Q hP hQ => simp only [map_add, hP, hQ]
  | mul_X P i hP => simp only [map_mul, MvPolynomial.map_X, aeval_X, hP]

/-- The actual original-coefficient homogeneous map into an
extension-valued affine infinity chart. -/
noncomputable def extendedProjectiveInfinityChartHom (b w z : Fin 3 → F) :
    MvPolynomial (Option (Fin 3)) E →ₐ[E] MvPolynomial (Fin 2) F :=
  aeval (fun j : Option (Fin 3) => j.elim 0 (boundaryAffineChartCoordinate b w z))

/-- The image of the entire original homogeneous closure ideal in
the actual extension-valued infinity chart. -/
noncomputable def extendedProjectiveInfinityChartIdeal
    (x : Fin 3 → G) (b w z : Fin 3 → F) : Ideal (MvPolynomial (Fin 2) F) :=
  Ideal.map (extendedProjectiveInfinityChartHom (E := E) b w z).toRingHom
    (projectiveConeIdeal (L := E) x)

/-- The original chart map factors through the specified coefficient
extension and then the actual same-coefficient chart substitution. -/
theorem extendedProjectiveInfinityChartHom_coefficient_extension
    (b w z : Fin 3 → F) (P : MvPolynomial (Option (Fin 3)) E) :
    extendedProjectiveInfinityChartHom (E := E) b w z P =
      projectiveInfinityChartHom b w z (MvPolynomial.map (algebraMap E F) P) :=
  (aeval_coefficient_extension _ P).symm

/-- This ideal is precisely the chart image of the original
homogeneous ideal after its specified coefficient extension. -/
theorem extendedProjectiveInfinityChartIdeal_eq_extended_ideal_chart
    (x : Fin 3 → G) (b w z : Fin 3 → F) :
    extendedProjectiveInfinityChartIdeal (E := E) x b w z =
      Ideal.map (projectiveInfinityChartHom b w z).toRingHom
        (Ideal.map (MvPolynomial.map (algebraMap E F)) (projectiveConeIdeal (L := E) x)) := by
  rw [Ideal.map_map]
  have he : (extendedProjectiveInfinityChartHom (E := E) b w z).toRingHom =
      (projectiveInfinityChartHom b w z).toRingHom.comp (MvPolynomial.map (algebraMap E F)) := by
    apply RingHom.ext
    intro P
    exact extendedProjectiveInfinityChartHom_coefficient_extension b w z P
  exact congrArg (fun phi : MvPolynomial (Option (Fin 3)) E →+* MvPolynomial (Fin 2) F =>
    Ideal.map phi (projectiveConeIdeal (L := E) x)) he

/-- Origin evaluation of this actual extension-valued chart is the
original projective equation evaluated at the original boundary vector. -/
theorem extendedProjectiveInfinityChartHom_origin
    (b w z : Fin 3 → F) (P : MvPolynomial (Option (Fin 3)) E) :
    aeval (fun _ : Fin 2 => (0 : F)) (extendedProjectiveInfinityChartHom (E := E) b w z P) =
      aeval (fun j : Option (Fin 3) => j.elim 0 b) P := by
  rw [extendedProjectiveInfinityChartHom_coefficient_extension, projectiveInfinityChartHom_origin]
  exact aeval_coefficient_extension _ P

/-- Actual closure membership over the original field constructs
the origin prime of the entire extension-valued chart ideal. -/
theorem extendedProjectiveInfinityChartIdeal_origin
    (x : Fin 3 → G) (b w z : Fin 3 → F) (hb : b ≠ 0)
    (hpoint : projectiveFieldPoint (E := E) (fun j : Option (Fin 3) => j.elim 0 b)
      (infinity_direction_projective_coordinates_ne_zero b hb) ∈ projectiveClosureSet (L := E) x) :
    extendedProjectiveInfinityChartIdeal (E := E) x b w z ≤
      RingHom.ker (aeval (fun _ : Fin 2 => (0 : F))).toRingHom := by
  apply Ideal.map_le_iff_le_comap.mpr
  intro P hP
  change aeval (fun _ : Fin 2 => (0 : F)) (extendedProjectiveInfinityChartHom (E := E) b w z P) = 0
  rw [extendedProjectiveInfinityChartHom_origin]
  exact projectiveClosureSet_all_coordinate_equations x _ _ hpoint P hP

/-- An original affine equation puts its actual coefficient-extended
leading equation inside the entire extension-valued chart ideal. -/
theorem extendedProjectiveInfinityChartIdeal_leading_equation
    (x : Fin 3 → G) (b w z : Fin 3 → F) (P : MvPolynomial (Fin 3) E)
    (d : ℕ) (hd : P.totalDegree ≤ d) (hP : aeval x P = 0) :
    aeval (boundaryAffineChartCoordinate b w z)
      (MvPolynomial.map (algebraMap E F) (homogeneousComponent d P)) ∈
        extendedProjectiveInfinityChartIdeal (E := E) x b w z := by
  have hhom : projectiveHomogenize P d ∈ projectiveConeIdeal (L := E) x := by
    apply (projectiveConeIdeal_mem_of_isHomogeneous x (projectiveHomogenize_isHomogeneous P d hd)).mpr
    rw [projectiveHomogenize_aeval_chart]
    exact hP
  have hm := Ideal.mem_map_of_mem (extendedProjectiveInfinityChartHom (E := E) b w z).toRingHom hhom
  change aeval (fun j : Option (Fin 3) => j.elim 0 (boundaryAffineChartCoordinate b w z))
    (projectiveHomogenize P d) ∈ extendedProjectiveInfinityChartIdeal (E := E) x b w z at hm
  rw [projectiveHomogenize_aeval_at_infinity P d hd] at hm
  rwa [aeval_coefficient_extension]

variable [CharZero E]

/-- Both original affine fiber equations construct both original
leading equations in the full extension-valued chart ideal. -/
theorem extendedProjectiveInfinityChartIdeal_original_boundary_equations
    (x : Fin 3 → G) (b w z : Fin 3 → F) (g v Lambda : Fin 3 → E)
    (B S : Matrix (Fin 3) (Fin 3) E) (T : Fin 3 → Fin 3 → Fin 3 → E) (q k : E)
    (hfactor : cubicFormPolynomial T = linearFormPolynomial Lambda * quadraticFormPolynomial B)
    (hQ : aeval x (quadraticFiberPolynomial g B q) = 0)
    (hC : aeval x (cubicFiberPolynomial v S T k) = 0) :
    aeval (boundaryAffineChartCoordinate b w z) (MvPolynomial.map (algebraMap E F)
      (homogeneousComponent 2 (quadraticFiberPolynomial g B q))) ∈
        extendedProjectiveInfinityChartIdeal (E := E) x b w z ∧
      aeval (boundaryAffineChartCoordinate b w z) (MvPolynomial.map (algebraMap E F)
        (modifiedBoundaryQuadric g Lambda S)) ∈
          extendedProjectiveInfinityChartIdeal (E := E) x b w z := by
  have hM : aeval x (modifiedCubicFiberPolynomial g v Lambda S q k) = 0 := by
    rw [modifiedCubicFiberPolynomial_elimination_identity g v Lambda B S T q k hfactor]
    simp only [map_add, map_mul, hQ, hC, mul_zero, zero_add]
  refine ⟨extendedProjectiveInfinityChartIdeal_leading_equation x b w z _ 2
    (quadraticFiberPolynomial_totalDegree g B q) hQ, ?_⟩
  have hm := extendedProjectiveInfinityChartIdeal_leading_equation x b w z _ 2
    (modifiedCubicFiberPolynomial_totalDegree g v Lambda S q k) hM
  rwa [modifiedBoundaryQuadric_eq_leading_component] at hm

/-- The full original closure ideal has the actual origin-local
length bound in a simple-root chart over any coefficient extension.
The original fiber's field need not contain the chart's coefficient field. -/
theorem original_closure_extended_infinity_chart_origin_local_bound
    (x : Fin 3 → G) (b w z : Fin 3 → F) (g v Lambda : Fin 3 → E) (hb : b ≠ 0)
    (hpoint : projectiveFieldPoint (E := E) (fun j : Option (Fin 3) => j.elim 0 b)
      (infinity_direction_projective_coordinates_ne_zero b hb) ∈ projectiveClosureSet (L := E) x)
    (B S : Matrix (Fin 3) (Fin 3) E) (T : Fin 3 → Fin 3 → Fin 3 → E) (q k : E)
    (hfactor : cubicFormPolynomial T = linearFormPolynomial Lambda * quadraticFormPolynomial B)
    (hQ : aeval x (quadraticFiberPolynomial g B q) = 0)
    (hC : aeval x (cubicFiberPolynomial v S T k) = 0)
    (scalar : F) (hscalar : scalar ≠ 0)
    (hfirst : aeval (boundaryAffineChartCoordinate b w z) (MvPolynomial.map (algebraMap E F)
      (homogeneousComponent 2 (quadraticFiberPolynomial g B q))) = C scalar * X 0 ^ 2)
    (hsecond : aeval (fun _ : Fin 2 => (0 : F)) (aeval (boundaryAffineChartCoordinate b w z)
      (MvPolynomial.map (algebraMap E F) (modifiedBoundaryQuadric g Lambda S))) = 0)
    (htransverse : aeval (fun _ : Fin 2 => (0 : F)) (pderiv 1 (aeval (boundaryAffineChartCoordinate b w z)
      (MvPolynomial.map (algebraMap E F) (modifiedBoundaryQuadric g Lambda S)))) ≠ 0) :
    ∃ hI : extendedProjectiveInfinityChartIdeal (E := E) x b w z ≤
        RingHom.ker (aeval (fun _ : Fin 2 => (0 : F))).toRingHom,
      let R := Localization.AtPrime (zeroPointQuotientPrime (extendedProjectiveInfinityChartIdeal (E := E) x b w z) hI)
      Module.Finite F R ∧ finrank F R ≤ 2 ∧ Module.length R R ≤ 2 := by
  have hI := extendedProjectiveInfinityChartIdeal_origin x b w z hb hpoint
  have hmem := extendedProjectiveInfinityChartIdeal_original_boundary_equations x b w z g v Lambda B S T q k hfactor hQ hC
  refine ⟨hI, ?_⟩
  exact boundary_equations_containing_ideal_origin_local_bound _ _ scalar hscalar hfirst hsecond htransverse
    (extendedProjectiveInfinityChartIdeal (E := E) x b w z) hI hmem.1 hmem.2

end DimensionFourDependence
