import DimensionFourDependence.AffineLevelGeometricIntegrality
import DimensionFourDependence.AffineTriangularDivisibility
import DimensionFourDependence.FiberAlgebraicBaseChange

/-! # Tangency at the actual generic level forces global annihilation

The actual source point retains exactly the coefficient-extended level
relation ideal over every algebraic parameter extension. Its prime ideal
is a minimal prime over the extended ideal; geometric integrality makes
that minimal prime unique. A tangent derivative vanishing at that point
is therefore divisible by the literal level equation, and the polynomial
flow obstruction makes it vanish identically.
-/

namespace DimensionFourDependence

open MvPolynomial

set_option maxHeartbeats 3000000
set_option synthInstance.maxHeartbeats 100000

variable {K F : Type*} [Field K] [CharZero K] [Field F] [Algebra K F]

attribute [-instance] IntermediateField.instSMulSubtypeMem in
/-- The actual source-chart point has exactly the extended level ideal
over every algebraic parameter coefficient field in any compatible ambient
field. Geometric integrality supplies uniqueness of the prime component. -/
theorem actual_affine_level_algebraic_source_relation_ideal
    {n : ℕ} (t : F) (ht : Transcendental K t) (x : Fin n → F)
    (hx : AlgebraicIndependent K x) (P : MvPolynomial (Fin n) K)
    (hvalue : t = aeval x P)
    (hclosed : algebraicClosure (IntermediateField.adjoin K {t}) F = ⊥)
    (E M : Type*) [Field E] [Field M]
    [Algebra (IntermediateField.adjoin K {t}) E]
    [Algebra.IsAlgebraic (IntermediateField.adjoin K {t}) E]
    [Algebra (IntermediateField.adjoin K {t}) M] [Algebra F M]
    [IsScalarTower (IntermediateField.adjoin K {t}) F M]
    [Algebra E M] [IsScalarTower (IntermediateField.adjoin K {t}) E M] :
    fiberVanishingIdeal (L := E) (fun i => algebraMap F M (x i)) =
      Ideal.span {MvPolynomial.map (algebraMap (IntermediateField.adjoin K {t}) E)
        (actualAffineLevelEquation t P)} := by
  let z := fun i => algebraMap F M (x i)
  have hsource : fiberVanishingIdeal (L := (IntermediateField.adjoin K {t})) z = fiberVanishingIdeal (L := (IntermediateField.adjoin K {t})) x := by
    ext B
    change aeval z B = 0 ↔ aeval x B = 0
    have he : aeval z B = algebraMap F M (aeval x B) := by
      exact (comp_aeval_apply (f := x) (IsScalarTower.toAlgHom (IntermediateField.adjoin K {t}) F M) B).symm
    rw [he, map_eq_zero_iff _ (algebraMap F M).injective]
  let J := Ideal.span {MvPolynomial.map (algebraMap (IntermediateField.adjoin K {t}) E) (actualAffineLevelEquation t P)}
  have hJ : extendCoefficientIdeal E (fiberVanishingIdeal (L := (IntermediateField.adjoin K {t})) z) = J := by
    rw [hsource, actual_affine_level_parameter_field_relation_ideal t ht x hx P hvalue]
    simp only [extendCoefficientIdeal, Ideal.map_span, Set.image_singleton, J]
  let : J.IsPrime := (Ideal.Quotient.isDomain_iff_prime _).mp
    (actual_affine_level_geometrically_integral t ht x hx P hvalue hclosed E)
  have hminimal := fiber_prime_minimal_after_algebraic_coefficients (L := (IntermediateField.adjoin K {t})) (E := E) z
  rw [hJ, Ideal.minimalPrimes_eq_subsingleton_self, Set.mem_singleton_iff] at hminimal
  exact hminimal

attribute [-instance] IntermediateField.instSMulSubtypeMem in
/-- Vanishing at the actual source point is exactly divisibility by the
literal affine level equation, also after algebraic coefficient extension. -/
theorem actual_affine_level_algebraic_source_zero_iff_dvd
    (t : F) (ht : Transcendental K t) (x : Fin 3 → F)
    (hx : AlgebraicIndependent K x) (P : MvPolynomial (Fin 3) K)
    (hvalue : t = aeval x P)
    (hclosed : algebraicClosure (IntermediateField.adjoin K {t}) F = ⊥)
    (E M : Type*) [Field E] [Field M]
    [Algebra (IntermediateField.adjoin K {t}) E]
    [Algebra.IsAlgebraic (IntermediateField.adjoin K {t}) E]
    [Algebra (IntermediateField.adjoin K {t}) M] [Algebra F M]
    [IsScalarTower (IntermediateField.adjoin K {t}) F M]
    [Algebra E M] [IsScalarTower (IntermediateField.adjoin K {t}) E M]
    (B : MvPolynomial (Fin 3) E) :
    aeval (fun i => algebraMap F M (x i)) B = 0 ↔
      MvPolynomial.map (algebraMap (IntermediateField.adjoin K {t}) E)
        (actualAffineLevelEquation t P) ∣ B := by
  change B ∈ fiberVanishingIdeal (L := E) (fun i => algebraMap F M (x i)) ↔ _
  rw [actual_affine_level_algebraic_source_relation_ideal t ht x hx P hvalue hclosed E M,
    Ideal.mem_span_singleton]

attribute [-instance] IntermediateField.instSMulSubtypeMem in
/-- An affine triangular field tangent at the actual generic level over
any algebraic parameter extension annihilates the whole coefficient-extended
original polynomial. Neither divisibility nor an eigenvalue is assumed. -/
theorem actual_affine_level_tangent_forces_global_annihilation
    (t : F) (ht : Transcendental K t) (x : Fin 3 → F)
    (hx : AlgebraicIndependent K x) (P : MvPolynomial (Fin 3) K)
    (hvalue : t = aeval x P)
    (hclosed : algebraicClosure (IntermediateField.adjoin K {t}) F = ⊥)
    (i : Fin 3) (hpartial : pderiv i P ≠ 0)
    (E M : Type*) [Field E] [Field M]
    [Algebra (IntermediateField.adjoin K {t}) E]
    [Algebra.IsAlgebraic (IntermediateField.adjoin K {t}) E]
    [Algebra (IntermediateField.adjoin K {t}) M] [Algebra F M]
    [IsScalarTower (IntermediateField.adjoin K {t}) F M]
    [Algebra E M] [IsScalarTower (IntermediateField.adjoin K {t}) E M]
    (u : Fin 2 → E) (b : Fin 3 → E)
    (htangent : aeval (fun j => algebraMap F M (x j))
      (affineProjectedTangentAction u b
        (MvPolynomial.map ((algebraMap (IntermediateField.adjoin K {t}) E).comp
          (algebraMap K (IntermediateField.adjoin K {t}))) P)) = 0) :
    affineProjectedTangentAction u b
      (MvPolynomial.map ((algebraMap (IntermediateField.adjoin K {t}) E).comp
        (algebraMap K (IntermediateField.adjoin K {t}))) P) = 0 := by
  let C := IntermediateField.adjoin K {t}
  let : CharZero C := charZero_of_injective_algebraMap (algebraMap K C).injective
  let : CharZero E := charZero_of_injective_algebraMap (algebraMap C E).injective
  let PE := MvPolynomial.map ((algebraMap C E).comp (algebraMap K C)) P
  let tE := algebraMap C E (IntermediateField.AdjoinSimple.gen K t)
  have heq : MvPolynomial.map (algebraMap C E) (actualAffineLevelEquation t P) = PE - MvPolynomial.C tE := by
    change MvPolynomial.map (algebraMap C E)
      (MvPolynomial.map (algebraMap K C) P - MvPolynomial.C (IntermediateField.AdjoinSimple.gen K t)) = _
    rw [map_sub, MvPolynomial.map_C, MvPolynomial.map_map]
  have hne : PE - MvPolynomial.C tE ≠ 0 := by
    rw [← heq]
    exact actualAffineLevelEquation_map_ne_zero_of_pderiv t P i hpartial E
  have hdiv := (actual_affine_level_algebraic_source_zero_iff_dvd t ht x hx P hvalue hclosed E M
    (affineProjectedTangentAction u b PE)).mp htangent
  rw [heq] at hdiv
  exact affine_triangular_level_tangency_forces_global_annihilation u b PE tE hne hdiv

end DimensionFourDependence
