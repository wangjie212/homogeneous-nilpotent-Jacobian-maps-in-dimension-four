import DimensionFourDependence.PrimitiveVectorGenericAvoidance
import DimensionFourDependence.GenericFiberCoprimeBase

/-! # The original primitive kernel has no zero on any geometric generic component -/

namespace DimensionFourDependence

open MvPolynomial

universe u
set_option maxHeartbeats 2500000
set_option synthInstance.maxHeartbeats 100000

variable {K : Type u} [Field K] [CharZero K]
local notation "R₀" => MvPolynomial (Fin 4) K
local notation "F₀" => FractionRing (MvPolynomial (Fin 4) K)

/-- Every actual point over the original full generic output avoids
the zero set of an original nonzero primitive polynomial vector.
The independent output triple is constructed from the original rank. -/
theorem original_rank_three_generic_output_point_primitive_vector_nonzero
    (H : Fin 4 → R₀) (hrank : polyRank (jac H) = 3)
    (u : Fin 4 → R₀) (hu : u ≠ 0) (hprim : IsPrimitiveVec u)
    (E : Type u) [Field E] [Algebra (polynomialOutputField H) E] [Algebra K E]
    [IsScalarTower K (polynomialOutputField H) E]
    (z : Fin 4 → E) (hpoint : ∀ i, aeval z (H i) = genericOutputValue H E i) :
    (fun i => aeval z (u i)) ≠ 0 := by
  let Q : Fin 4 → F₀ := fun i => algebraMap R₀ F₀ (H i)
  have hrQ : (rationalJacobian Q).rank = 3 := by
    rw [rationalJacobian_polynomial H]
    exact hrank
  obtain ⟨s, _hs, hY, _hAlg⟩ := exists_independent_output_triple Q hrQ
  let M := polynomialOutputField H
  let y : Fin 3 → M := fun i => fullOutputCoordinate (K := K) Q (s i)
  have hy : AlgebraicIndependent K y := by
    apply AlgebraicIndependent.of_comp M.val
    exact hY
  have hyE := hy.map' (f := IsScalarTower.toAlgHom K M E) (algebraMap M E).injective
  change AlgebraicIndependent K (fun i => genericOutputValue H E (s i)) at hyE
  apply three_independent_polynomial_values_avoid_primitive_vector_zero z
    (fun i : Fin 3 => H (s i)) _ u hu hprim
  simpa only [hpoint] using hyE

/-- The original nonzero primitive vector has no zero at any point of
the entire actual geometric generic component zero locus. -/
theorem original_geometric_component_primitive_vector_nowhere_zero
    (H : Fin 4 → R₀) (hrank : polyRank (jac H) = 3)
    (u : Fin 4 → R₀) (hu : u ≠ 0) (hprim : IsPrimitiveVec u)
    (E : Type u) [Field E] [Algebra (polynomialOutputField H) E] [Algebra K E]
    [IsScalarTower K (polynomialOutputField H) E]
    (P : Ideal (MvPolynomial (Fin 4) E)) [P.IsPrime]
    (hP : P ∈ (extendCoefficientIdeal E (fiberVanishingIdeal
      (L := polynomialOutputField H) (rationalCoordinate (K := K) (n := 4)))).minimalPrimes)
    (z : Fin 4 → E) (hz : ∀ Q ∈ P, aeval z Q = 0) :
    (fun i => aeval z (u i)) ≠ 0 :=
  original_rank_three_generic_output_point_primitive_vector_nonzero H hrank u hu hprim E z
    (geometric_component_zero_locus_original_output H E P hP z hz)

/-- The original homogeneous rank-three map constructs its own actual
primitive homogeneous right kernel and its nonvanishing at every point
over the full original generic output. -/
theorem original_homogeneous_rank_three_map_constructs_nowhere_zero_primitive_kernel
    (H : Fin 4 → R₀) {d : ℕ} (hH : IsHomogMap H d) (hrank : polyRank (jac H) = 3)
    (E : Type u) [Field E] [Algebra (polynomialOutputField H) E] [Algebra K E]
    [IsScalarTower K (polynomialOutputField H) E] :
    ∃ (u : Fin 4 → R₀) (e : ℕ), IsPrimRightKernel (jac H) u e ∧
      ∀ z : Fin 4 → E, (∀ i, aeval z (H i) = genericOutputValue H E i) →
        (fun i => aeval z (u i)) ≠ 0 := by
  obtain ⟨u, e, hu⟩ := exists_primRightKernel (jac H) (fun i j => (hH i).pderiv (i := j))
    (by rw [hrank]; norm_num)
  exact ⟨u, e, hu, fun z hpoint => original_rank_three_generic_output_point_primitive_vector_nonzero
    H hrank u hu.ne_zero hu.prim E z hpoint⟩

end DimensionFourDependence
