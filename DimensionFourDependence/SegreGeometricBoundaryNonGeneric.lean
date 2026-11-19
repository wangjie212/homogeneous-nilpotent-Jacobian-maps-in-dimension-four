import DimensionFourDependence.SegreGenericRulingExclusion
import DimensionFourDependence.GenericFiberOutput
import DimensionFourDependence.SegreOriginalOutputChart

/-! # Geometric Segre boundary directions on either ruling are nongeneric -/

namespace DimensionFourDependence

open MvPolynomial
attribute [local instance] MvPolynomial.gradedAlgebra

universe u
set_option maxHeartbeats 3000000

variable {K : Type u} [Field K] [CharZero K]

/-- The actual geometric generic output retains its original projective
generic point after every compatible extension of the constants. -/
theorem geometric_output_extended_projective_generic
    (H : Fin 4 → MvPolynomial (Fin 4) K) {d : ℕ} (hd : 0 < d)
    (hH : IsHomogMap H d) (hH0 : H ≠ 0)
    (E : Type u) [Field E] [Algebra (polynomialOutputField H) E]
    [Algebra K E] [IsScalarTower K (polynomialOutputField H) E]
    (κ : Type u) [Field κ] [Algebra E κ] [Algebra K κ] [IsScalarTower K E κ]
    (hy : (fun i => algebraMap E κ (genericOutputValue H E i)) ≠ 0) :
    projectiveFieldPoint (E := K) (fun i => algebraMap E κ (genericOutputValue H E i)) hy =
      projectiveImageGenericPoint H hd hH hH0 := by
  apply ProjectiveSpectrum.ext
  apply HomogeneousIdeal.ext'
  intro m R hR
  change R.IsHomogeneous m at hR
  rw [projectiveFieldPoint_homogeneous_mem _ hy R hR]
  change aeval (fun i => algebraMap E κ (genericOutputValue H E i)) R = 0 ↔ aeval H R = 0
  have he := comp_aeval_apply (genericOutputValue H E) (IsScalarTower.toAlgHom K E κ) R
  change algebraMap E κ (aeval (genericOutputValue H E) R) =
    aeval (fun i => algebraMap E κ (genericOutputValue H E i)) R at he
  rw [← he]
  exact (map_eq_zero_iff _ (algebraMap E κ).injective).trans (genericOutputValue_relations H E R)

/-- Every actual boundary direction of an original geometric Segre
component preserving either target ruling is nongeneric over the original
field. The homogeneous primitive map and all its cross equations are constructed. -/
theorem original_segre_geometric_boundary_ruling_genericity_exclusion
    (H : Fin 4 → MvPolynomial (Fin 4) K) {d : ℕ} (hd : 0 < d) (hH : IsHomogMap H d)
    (hN : IsNilpotent (jac H)) (hrank : polyRank (jac H) = 3)
    (hind : ¬ComponentsDependent H) (I : ImageRelationWitness H)
    (hSegre : H 0 * H 3 - H 1 * H 2 = 0)
    (E : Type u) [Field E] [Algebra (polynomialOutputField H) E]
    [Algebra K E] [IsScalarTower K (polynomialOutputField H) E]
    (Q : Ideal (MvPolynomial (Fin 4) E)) [Q.IsPrime]
    (hQ : Q ∈ (extendCoefficientIdeal E (fiberVanishingIdeal
      (L := polynomialOutputField H) (rationalCoordinate (K := K) (n := 4)))).minimalPrimes)
    (κ : Type u) [Field κ] [Algebra E κ] [Algebra K κ] [IsScalarTower K E κ]
    (z : Option (Fin 4) → κ) (hz : z ≠ 0) (hb : (fun i => z (some i)) ≠ 0)
    (hboundary : projectiveFieldPoint (E := E) z hz ∈
      projectiveClosureSet (L := E) (primeQuotientCoordinate Q))
    (r : Fin 4) (hr : r = 1 ∨ r = 2)
    (hruling : algebraMap E κ (genericOutputValue H E 0) * z (some r) -
      algebraMap E κ (genericOutputValue H E r) * z (some 0) = 0) :
    projectiveFieldPoint (E := K) (fun i => z (some i)) hb ≠
      projectiveImageGenericPoint H hd hH (rank_three_polynomial_map_ne_zero H hrank) := by
  intro hgeneric
  have hH0 := rank_three_polynomial_map_ne_zero H hrank
  obtain ⟨G, P, c, hc, hG, hGh, hP, hprim, hHP, _hdeg⟩ :=
    exists_primitive_factorization_common_degree_le_sub_two H hH hind I
  have hext := primitive_boundary_cross_equations
    (fun i => MvPolynomial.map (algebraMap K E) (H i))
    (fun i => MvPolynomial.map (algebraMap K E) (P i))
    (MvPolynomial.map (algebraMap K E) G) (fun i => (hP i).map (algebraMap K E))
    (by funext i; rw [congrFun hHP i, map_mul]) (primeQuotientCoordinate Q) (genericOutputValue H E)
    (genericOutputValue_ne_zero H hH0 E)
    (geometric_component_generic_output_evaluation H E Q hQ) z hz hboundary
  have hcross (i j : Fin 4) : algebraMap E κ (genericOutputValue H E i) *
      aeval (fun l => z (some l)) (P j) - algebraMap E κ (genericOutputValue H E j) *
        aeval (fun l => z (some l)) (P i) = 0 := by
    simpa only [aeval_map_algebra_extension] using hext i j
  have hy : (fun i => algebraMap E κ (genericOutputValue H E i)) ≠ 0 := by
    intro he
    apply genericOutputValue_ne_zero H hH0 E
    funext i
    apply (algebraMap E κ).injective
    simpa only [map_zero, Pi.zero_apply] using congrFun he i
  exact no_generic_original_segre_direction_with_same_ruling_target H hd hH hN hrank hind I hSegre hH0
    G hG c hGh P (by omega) hP hprim hHP (Nat.add_sub_of_le (hc.trans (Nat.sub_le d 2)))
    (fun i => z (some i)) (fun i => algebraMap E κ (genericOutputValue H E i)) hb hy
    hgeneric (geometric_output_extended_projective_generic H hd hH hH0 E κ hy) hcross r hr hruling

end DimensionFourDependence
