import DimensionFourDependence.SegreGeometricBoundaryNonGeneric
import DimensionFourDependence.SegreMappedRulingAlgebraicity
import DimensionFourDependence.SegreOriginalFiberWitness

/-! # Actual geometric Segre boundary coordinates are algebraic over the original parameter -/

namespace DimensionFourDependence

open MvPolynomial Matrix
attribute [local instance] coefficientFieldScalarTower MvPolynomial.gradedAlgebra

universe u
set_option maxHeartbeats 3000000
set_option synthInstance.maxHeartbeats 100000

variable {K : Type u} [Field K] [CharZero K]

/-- Every normalized actual geometric boundary point on either original
Segre ruling is algebraic over that exact original ruling parameter.
The coefficient embedding, primitive-map exclusion and line density are
all constructed from the original homogeneous nilpotent map. -/
theorem original_segre_geometric_boundary_coordinates_algebraic_over_ruling_parameter
    (H : Fin 4 → MvPolynomial (Fin 4) K) {d : ℕ} (hd : 0 < d) (hH : IsHomogMap H d)
    (hN : IsNilpotent (jac H)) (hrank : polyRank (jac H) = 3)
    (hind : ¬ComponentsDependent H) (I : ImageRelationWitness H)
    (hSegre : H 0 * H 3 - H 1 * H 2 = 0)
    (E : Type u) [Field E] [IsAlgClosed E] [Algebra (polynomialOutputField H) E]
    [Algebra K E] [IsScalarTower K (polynomialOutputField H) E]
    (Q : Ideal (MvPolynomial (Fin 4) E)) [Q.IsPrime]
    (hQ : Q ∈ (extendCoefficientIdeal E (fiberVanishingIdeal
      (L := polynomialOutputField H) (rationalCoordinate (K := K) (n := 4)))).minimalPrimes)
    (j : Fin 3) (hj : j ≠ 0)
    (κ : Type u) [Field κ] [Algebra E κ] [Algebra K κ] [IsScalarTower K E κ]
    (z : Option (Fin 4) → κ) (hz : z ≠ 0) (a : Fin 4) (ha : z (some a) = 1)
    (hboundary : projectiveFieldPoint (E := E) z hz ∈
      projectiveClosureSet (L := E) (primeQuotientCoordinate Q))
    (hkernel : segreRulingMatrix j
      (algebraMap E κ (genericOutputValue H E j.castSucc / genericOutputValue H E 0)) *ᵥ
        (fun i => z (some i)) = 0) :
    ∀ i, IsAlgebraic (IntermediateField.adjoin K
      ({algebraMap E κ (genericOutputValue H E j.castSucc / genericOutputValue H E 0)} : Set κ))
        (z (some i)) := by
  obtain ⟨hY, c, q, k, hc, hq, hk, _he, _hce, _hqe⟩ :=
    exists_original_segre_weighted_fiber_invariants H hd hH hN hrank hind hSegre
  obtain ⟨R⟩ := segre_original_fiber_invariants_geometric_realization
    H hind hSegre hY c q k hc hq hk hrank E Q hQ
  let g : coefficientField (K := K) (segreOriginalOutputTriple H) →ₐ[K] E :=
    { toRingHom := R.coefficientMap, commutes' := R.scalar_image }
  let f := (IsScalarTower.toAlgHom K E κ).comp g
  have ht : f (segreCoefficientRulingParameter (segreOriginalOutputTriple H) j) =
      algebraMap E κ (genericOutputValue H E j.castSucc / genericOutputValue H E 0) := by
    change algebraMap E κ (R.coefficientMap (coefficientCoordinate (K := K) (segreOriginalOutputTriple H) j /
      coefficientCoordinate (K := K) (segreOriginalOutputTriple H) 0)) = _
    rw [map_div₀, R.coordinate_image, R.coordinate_image]
    rfl
  have hb : (fun i => z (some i)) ≠ 0 := by
    intro he
    exact one_ne_zero (ha.symm.trans (congrFun he a))
  have hy0 : genericOutputValue H E 0 ≠ 0 := by
    intro he
    have hzero : H 0 = 0 := by
      simpa only [aeval_X] using (genericOutputValue_relations H E (X 0)).mp (by
        simpa only [aeval_X] using he)
    exact (linearIndependent_of_componentsIndependent H hind).ne_zero 0 hzero
  have hyκ : algebraMap E κ (genericOutputValue H E 0) ≠ 0 :=
    (map_ne_zero (algebraMap E κ)).mpr hy0
  have hrel := segreRulingMatrix_kernel_coordinate_relation j hj _ (fun i => z (some i)) hkernel
  have hr : j.castSucc = 1 ∨ j.castSucc = 2 := by
    fin_cases j
    · exact False.elim (hj rfl)
    · exact Or.inl rfl
    · exact Or.inr rfl
  have hruling : algebraMap E κ (genericOutputValue H E 0) * z (some j.castSucc) -
      algebraMap E κ (genericOutputValue H E j.castSucc) * z (some 0) = 0 := by
    rw [hrel, map_div₀]
    field_simp [hyκ] <;> ring
  have hng := original_segre_geometric_boundary_ruling_genericity_exclusion
    H hd hH hN hrank hind I hSegre E Q hQ κ z hz hb hboundary j.castSucc hr hruling
  exact nongeneric_normalized_segre_point_algebraic_over_mapped_parameter
    H hY hd hH (rank_three_polynomial_map_ne_zero H hrank) hind hSegre j hj κ f _ ht
      (fun i => z (some i)) hb a ha hkernel hng

end DimensionFourDependence
