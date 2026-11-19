import DimensionFourDependence.ProjectiveLineAtlasPoints
import DimensionFourDependence.GenericVertexLine

/-! # Constant planes and vertices are excluded at an actual generic atlas line

A contained linear subspace gives every affine line identity within it.
Consequently Gauss dimension two excludes a fixed nonzero original-field
vertex on a line through the actual generic image point. Component
independence likewise excludes containment in an original-field hyperplane.
-/

namespace DimensionFourDependence

open MvPolynomial

variable {K E : Type*} [Field K] [Field E] [Algebra K E]

/-- Pointwise containment of a linear subspace gives the full polynomial
identity of every affine line in it over an infinite field. -/
theorem contained_subspace_affine_line_identity [Infinite E]
    (R : MvPolynomial (Fin 4) K) (L : Submodule E (Fin 4 → E))
    (hL : ∀ x ∈ L, aeval x R = 0) (O D : Fin 4 → E) (hO : O ∈ L) (hD : D ∈ L) :
    aeval (fun i => Polynomial.C (O i) + Polynomial.C (D i) * Polynomial.X) R = 0 := by
  apply Polynomial.funext
  intro t
  rw [Polynomial.eval_zero]
  change Polynomial.aeval t (aeval (fun i => Polynomial.C (O i) + Polynomial.C (D i) * Polynomial.X) R) = 0
  rw [polynomial_affine_line_aeval]
  exact hL _ (L.add_mem hO (L.smul_mem t hD))

/-- Membership of a point and direction in an actual atlas line supplies
the affine line identity in the original equation over the original field. -/
theorem atlas_line_point_direction_identity [Infinite E]
    (R : MvPolynomial (Fin 4) K)
    (s : hypersurfaceLineAtlas (MvPolynomial.map (algebraMap K E) R))
    (O D : Fin 4 → E) (hO : O ∈ hypersurfaceAtlasLine _ s) (hD : D ∈ hypersurfaceAtlasLine _ s) :
    aeval (fun i => Polynomial.C (O i) + Polynomial.C (D i) * Polynomial.X) R = 0 := by
  apply contained_subspace_affine_line_identity R (hypersurfaceAtlasLine _ s) _ O D hO hD
  intro x hx
  have he := hypersurfaceAtlasLine_contained _ s x hx
  simpa only [aeval_map_algebra_extension] using he

/-- The actual generic image point satisfies no nonzero constant linear
relation when the original polynomial components are independent. -/
theorem genericOutputValue_no_constant_linear_relation
    (H : Fin 4 → MvPolynomial (Fin 4) K) (hind : ¬ ComponentsDependent H)
    [Algebra (polynomialOutputField H) E] [IsScalarTower K (polynomialOutputField H) E]
    (ν : Fin 4 → K) (hν : ν ≠ 0) :
    (∑ i, algebraMap K E (ν i) * genericOutputValue H E i) ≠ 0 := by
  intro hzero
  let L : MvPolynomial (Fin 4) K := ∑ i, MvPolynomial.C (ν i) * X i
  have hgeneric : aeval (genericOutputValue H E) L = 0 := by
    simpa only [L, map_sum, map_mul, aeval_C, aeval_X] using hzero
  have hsource := (genericOutputValue_relations H E L).mp hgeneric
  apply hind
  refine ⟨ν, hν, ?_⟩
  simpa only [L, map_sum, map_mul, aeval_C, aeval_X, algebraMap_eq, MvPolynomial.smul_eq_C_mul] using hsource

/-- A line through the actual generic image cannot be contained in a fixed
original-field hyperplane when the original components are independent. -/
theorem generic_atlas_line_not_in_constant_hyperplane
    (H : Fin 4 → MvPolynomial (Fin 4) K) (hind : ¬ ComponentsDependent H)
    [Algebra (polynomialOutputField H) E] [IsScalarTower K (polynomialOutputField H) E]
    (I : ImageRelationWitness H)
    (s : hypersurfaceLineAtlas (MvPolynomial.map (algebraMap K E) I.equation))
    (hpoint : genericOutputValue H E ∈ hypersurfaceAtlasLine _ s) (ν : Fin 4 → K) (hν : ν ≠ 0) :
    ¬ ∀ x ∈ hypersurfaceAtlasLine _ s, (∑ i, algebraMap K E (ν i) * x i) = 0 := by
  intro hplane
  exact genericOutputValue_no_constant_linear_relation H hind ν hν (hplane _ hpoint)

variable [CharZero K]

/-- Gauss dimension two excludes every fixed nonzero original-field vertex
from every actual atlas line through the actual generic image point. -/
theorem gauss_dimension_two_generic_atlas_line_no_constant_vertex
    (H : Fin 4 → MvPolynomial (Fin 4) K)
    [Algebra (polynomialOutputField H) E] [IsScalarTower K (polynomialOutputField H) E]
    {d : ℕ} (hd : 0 < d) (hH : IsHomogMap H d)
    (hN : IsNilpotent (jac H)) (hrank : polyRank (jac H) = 3)
    (I : ImageRelationWitness H) (hGauss : gaussImageDimension H I = 2)
    (s : hypersurfaceLineAtlas (MvPolynomial.map (algebraMap K E) I.equation))
    (hpoint : genericOutputValue H E ∈ hypersurfaceAtlasLine _ s) (C : Fin 4 → K) (hC : C ≠ 0) :
    (fun i => algebraMap K E (C i)) ∉ hypersurfaceAtlasLine _ s := by
  let : CharZero E := charZero_of_injective_algebraMap (algebraMap K E).injective
  intro hvertex
  exact gauss_dimension_two_no_generic_vertex_line (E := E) H hd hH hN hrank I hGauss C hC
    (atlas_line_point_direction_identity I.equation s _ _ hpoint hvertex)

end DimensionFourDependence
