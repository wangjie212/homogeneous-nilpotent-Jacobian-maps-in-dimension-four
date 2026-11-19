import DimensionFourDependence.SegreBoundaryRulingAlgebraicity

/-! # Actual original Segre boundary coordinates are algebraic over their ruling parameter -/

namespace DimensionFourDependence

open MvPolynomial Matrix
attribute [local instance] coefficientFieldScalarTower MvPolynomial.gradedAlgebra

universe u
set_option maxHeartbeats 3000000
set_option synthInstance.maxHeartbeats 100000
set_option quotPrecheck false

variable {K : Type u} [Field K] [CharZero K]
local notation "S₀" => FractionRing (MvPolynomial (Fin 4) K)

/-- Section 5.2's algebraicity assertion for every actual normalized
full-fiber boundary direction on either original ruling. The primitive
factorization, target cross equations, genericity exclusion and ruling
dimension are all constructed from the original map and actual boundary. -/
theorem actual_full_fiber_segre_boundary_coordinates_algebraic_over_ruling_field
    (H : Fin 4 → MvPolynomial (Fin 4) K) (hrank : polyRank (jac H) = 3)
    (hY : AlgebraicIndependent K (segreOriginalOutputTriple H))
    {d : ℕ} (hd : 0 < d) (hH : IsHomogMap H d)
    (hN : IsNilpotent (jac H)) (hind : ¬ComponentsDependent H) (I : ImageRelationWitness H)
    (hSegre : H 0 * H 3 - H 1 * H 2 = 0)
    (j : Fin 3) (hj : j ≠ 0)
    (κ : Type u) [Field κ] [Algebra (coefficientField (K := K) (segreOriginalOutputTriple H)) κ] [Algebra K κ] [IsScalarTower K (coefficientField (K := K) (segreOriginalOutputTriple H)) κ]
    (z : Option (Fin 4) → κ) (hz : z ≠ 0) (a : Fin 4) (ha : z (some a) = 1)
    (hboundary : projectiveFieldPoint (E := (coefficientField (K := K) (segreOriginalOutputTriple H))) z hz ∈ projectiveClosureSet (L := (coefficientField (K := K) (segreOriginalOutputTriple H))) (rationalCoordinate (K := K) (n := 4)))
    (hkernel : (segreRulingMatrix j (segreRulingFieldParameter (segreOriginalOutputTriple H) hY j hj)).map
      ((algebraMap (coefficientField (K := K) (segreOriginalOutputTriple H)) κ).comp (segreRulingFieldCoefficientHom (segreOriginalOutputTriple H) hY j hj).toRingHom) *ᵥ
        (fun i => z (some i)) = 0) :
    ∀ i, IsAlgebraic (segreBoundaryRulingField (segreOriginalOutputTriple H) hY j hj κ) (z (some i)) := by
  letI : Algebra (coefficientField (K := K) (fun i : Fin 3 =>
      algebraMap (MvPolynomial (Fin 4) K) S₀ (H i.castSucc))) κ :=
    inferInstanceAs (Algebra (coefficientField (K := K) (segreOriginalOutputTriple H)) κ)
  letI : IsScalarTower K (coefficientField (K := K) (fun i : Fin 3 =>
      algebraMap (MvPolynomial (Fin 4) K) S₀ (H i.castSucc))) κ :=
    inferInstanceAs (IsScalarTower K (coefficientField (K := K) (segreOriginalOutputTriple H)) κ)
  have hb : (fun i => z (some i)) ≠ 0 := by
    intro he
    have hz0 := congrFun he a
    exact one_ne_zero (ha.symm.trans hz0)
  have hcoord (i : Fin 3) : (actualChartOutputCoordinate H hrank (Equiv.refl (Fin 4)) hY) i.castSucc = coefficientCoordinate (K := K) (segreOriginalOutputTriple H) i := by
    apply (algebraMap (coefficientField (K := K) (segreOriginalOutputTriple H)) S₀).injective
    rfl
  have hcoord0 : (actualChartOutputCoordinate H hrank (Equiv.refl (Fin 4)) hY) 0 = coefficientCoordinate (K := K) (segreOriginalOutputTriple H) 0 := hcoord 0
  have hU0 : coefficientCoordinate (K := K) (segreOriginalOutputTriple H) 0 ≠ 0 := by
    intro he
    apply (hY.transcendental 0).ne_zero
    simpa only [coefficientCoordinate_coe, IntermediateField.coe_zero] using
      congrArg (fun l : (coefficientField (K := K) (segreOriginalOutputTriple H)) => (l : S₀)) he
  have hUκ : algebraMap (coefficientField (K := K) (segreOriginalOutputTriple H)) κ (coefficientCoordinate (K := K) (segreOriginalOutputTriple H) 0) ≠ 0 :=
    (map_ne_zero (algebraMap (coefficientField (K := K) (segreOriginalOutputTriple H)) κ)).mpr hU0
  let φ := (algebraMap (coefficientField (K := K) (segreOriginalOutputTriple H)) κ).comp (segreRulingFieldCoefficientHom (segreOriginalOutputTriple H) hY j hj).toRingHom
  have hk : segreRulingMatrix j (φ (segreRulingFieldParameter (segreOriginalOutputTriple H) hY j hj)) *ᵥ
      (fun i => z (some i)) = 0 := by
    rw [← segreRulingMatrix_map]
    exact hkernel
  have hparam : φ (segreRulingFieldParameter (segreOriginalOutputTriple H) hY j hj) =
      algebraMap (coefficientField (K := K) (segreOriginalOutputTriple H)) κ (segreCoefficientRulingParameter (segreOriginalOutputTriple H) j) := by
    change algebraMap (coefficientField (K := K) (segreOriginalOutputTriple H)) κ (segreRulingFieldCoefficientHom (segreOriginalOutputTriple H) hY j hj
      (segreRulingFieldParameter (segreOriginalOutputTriple H) hY j hj)) = _
    rw [segreRulingFieldCoefficientHom_parameter]
  have hrel := segreRulingMatrix_kernel_coordinate_relation j hj _ (fun i => z (some i)) hk
  rw [hparam] at hrel
  have hr : j.castSucc = 1 ∨ j.castSucc = 2 := by
    fin_cases j
    · exact False.elim (hj rfl)
    · exact Or.inl rfl
    · exact Or.inr rfl
  have hruling : algebraMap (coefficientField (K := K) (segreOriginalOutputTriple H)) κ ((actualChartOutputCoordinate H hrank (Equiv.refl (Fin 4)) hY) 0) * z (some j.castSucc) -
      algebraMap (coefficientField (K := K) (segreOriginalOutputTriple H)) κ ((actualChartOutputCoordinate H hrank (Equiv.refl (Fin 4)) hY) j.castSucc) * z (some 0) = 0 := by
    rw [hrel, hcoord j, hcoord0, segreCoefficientRulingParameter, map_div₀]
    field_simp [hUκ] <;> ring
  have hng := original_segre_full_boundary_ruling_genericity_exclusion H hrank hY hd hH hN hind I hSegre
    κ z hz hb hboundary j.castSucc hr hruling
  exact nongeneric_normalized_original_segre_ruling_point_isAlgebraic H hY hd hH
    (rank_three_polynomial_map_ne_zero H hrank) hind hSegre j hj κ (fun i => z (some i)) hb a ha hkernel hng

end DimensionFourDependence
