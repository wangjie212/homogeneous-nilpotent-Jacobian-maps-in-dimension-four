import DimensionFourDependence.SegreOriginalFirstRulingExclusion
import DimensionFourDependence.SegreRulingTranspose
import DimensionFourDependence.ProjectiveRestrictionKernelCriterion

/-! # Lemma 5.2 for both original Segre rulings -/

namespace DimensionFourDependence

open MvPolynomial

set_option maxHeartbeats 3000000
set_option quotPrecheck false

universe u
variable {K : Type u} [Field K] [CharZero K]
  (H : Fin 4 → MvPolynomial (Fin 4) K) {d : ℕ} (hd : 0 < d) (hH : IsHomogMap H d)
  (hrank : polyRank (jac H) = 3) (hind : ¬ComponentsDependent H) (I : ImageRelationWitness H)
  (hSegre : H 0 * H 3 - H 1 * H 2 = 0)

local notation "R₀" => MvPolynomial (Fin 4) K
local notation "Q₀" => segreOriginalSourceDeterminantPrime H hd hH hrank hind I hSegre
local notation "e₀" => segreTransposePolynomialEquiv (K := K)
local notation "T₀" => segreTransposeMatrix (K := K)

/-- Transposing the actual source and target exchanges the two rulings
and transports projective dominance, primitive factorization and nilpotence.
The first-ruling contradiction therefore excludes the second ruling too. -/
theorem no_dominant_original_segre_second_ruling_cross_relation
    (hN : IsNilpotent (jac H)) (hH0 : H ≠ 0)
    (G : R₀) (hG : G ≠ 0) (c : ℕ) (hGh : G.IsHomogeneous c)
    (P : Fin 4 → R₀) {m : ℕ} (hm : 0 < m) (hP : IsHomogMap P m)
    (hprim : IsPrimitiveVec P) (hHP : H = fun i => G * P i) (hcm : c + m = d)
    (hdom : originalProjectiveRestrictionDominant H hd hH hH0 hrank I P hm hP hprim)
    (hcross : P 1 * X 0 - P 0 * X 1 ∈ (Q₀).asIdeal) : False := by
  let H' := segreTransposeMap H
  let P' := segreTransposeMap P
  have hH' : IsHomogMap H' d := linearPolynomialConjugate_homogeneous (T₀) (T₀) H hH
  have hP' : IsHomogMap P' m := linearPolynomialConjugate_homogeneous (T₀) (T₀) P hP
  have hN' : IsNilpotent (jac H') := linearPolynomialConjugate_nilpotent (T₀) (T₀)
    segreTransposeMatrix_square segreTransposeMatrix_square H hN
  have hrank' : polyRank (jac H') = 3 :=
    (linearPolynomialConjugate_polyRank (T₀) (T₀) segreTransposeMatrix_square segreTransposeMatrix_square H).trans hrank
  have hind' : ¬ComponentsDependent H' := linearPolynomialConjugate_componentsIndependent (T₀) (T₀)
    segreTransposeMatrix_square segreTransposeMatrix_square H hind
  let I' : ImageRelationWitness H' := I.linearConjugate H (T₀) (T₀) segreTransposeMatrix_square segreTransposeMatrix_square
  have hH0' : H' ≠ 0 := segreTransposeMap_ne_zero H hH0
  have hprim' : IsPrimitiveVec P' := segreTransposeMap_primitive P hprim
  have hSegre' : H' 0 * H' 3 - H' 1 * H' 2 = 0 := by
    have he := congrArg (e₀) hSegre
    simp only [map_sub, map_mul, map_zero] at he
    simpa [H', segreTransposeMap_coordinate, segreTransposeIndex, Equiv.swap_apply_def, mul_comm] using he
  have hG' : (e₀) G ≠ 0 := by
    intro hz
    apply hG
    apply (e₀).injective
    simpa only [map_zero] using hz
  have hGh' : ((e₀) G).IsHomogeneous c := linearPolynomialPullback_homogeneous (T₀) G hGh
  have hHP' : H' = fun i => (e₀) G * P' i := by
    funext i
    simp only [H', P', segreTransposeMap_coordinate, hHP, map_mul]
  have hdom' : originalProjectiveRestrictionDominant H' hd hH' hH0' hrank' I' P' hm hP' hprim' := by
    apply original_projective_restriction_dominant_of_cone_kernel H' hd hH' hH0' hrank' I' P' hm hP' hprim'
    intro z
    rw [original_segre_image_relation_ideal_eq_determinant_prime H' hd hH' hrank' hind' I' hSegre']
    change aeval P' z ∈ Ideal.span {standardRulingPolynomial (F := K)} ↔ z ∈ Ideal.span {standardRulingPolynomial (F := K)}
    rw [show aeval P' z = (e₀) (aeval P ((e₀) z)) from segreTransposeMap_substitution P z,
      segreTransposePolynomialEquiv_mem_determinant_prime]
    have he := segre_projective_restriction_dominance_constructs_kernel H hd hH hrank hind I hSegre hH0 P hm hP hprim hdom ((e₀) z)
    change aeval P ((e₀) z) ∈ Ideal.span {standardRulingPolynomial (F := K)} ↔
      (e₀) z ∈ Ideal.span {standardRulingPolynomial (F := K)} at he
    rw [he, segreTransposePolynomialEquiv_mem_determinant_prime]
  have hcross' : P' 2 * X 0 - P' 0 * X 2 ∈
      (segreOriginalSourceDeterminantPrime H' hd hH' hrank' hind' I' hSegre').asIdeal := by
    change P' 2 * X 0 - P' 0 * X 2 ∈ Ideal.span {standardRulingPolynomial (F := K)}
    have he : P' 2 * X 0 - P' 0 * X 2 = (e₀) (P 1 * X 0 - P 0 * X 1) := by
      simp [P', segreTransposeMap_coordinate, map_sub, map_mul,
        segreTransposePolynomialEquiv_coordinate, segreTransposeIndex, Equiv.swap_apply_def]
    rw [he, segreTransposePolynomialEquiv_mem_determinant_prime]
    exact hcross
  exact no_dominant_original_segre_first_ruling_cross_relation H' hd hH' hrank' hind' I' hSegre'
    hN' hH0' ((e₀) G) hG' c hGh' P' hm hP' hprim' hHP' hcm hdom' hcross'

/-- Lemma 5.2 in the paper's Segre coordinates: a dominant primitive
restriction of the original homogeneous nilpotent map preserves neither
of the two actual quadric ruling parameters. -/
theorem lemma_5_2_segre_cross_relations
    (hN : IsNilpotent (jac H)) (hH0 : H ≠ 0)
    (G : R₀) (hG : G ≠ 0) (c : ℕ) (hGh : G.IsHomogeneous c)
    (P : Fin 4 → R₀) {m : ℕ} (hm : 0 < m) (hP : IsHomogMap P m)
    (hprim : IsPrimitiveVec P) (hHP : H = fun i => G * P i) (hcm : c + m = d)
    (hdom : originalProjectiveRestrictionDominant H hd hH hH0 hrank I P hm hP hprim) :
    (P 2 * X 0 - P 0 * X 2 ∉ (Q₀).asIdeal) ∧
      (P 1 * X 0 - P 0 * X 1 ∉ (Q₀).asIdeal) := by
  constructor
  · exact no_dominant_original_segre_first_ruling_cross_relation H hd hH hrank hind I hSegre
      hN hH0 G hG c hGh P hm hP hprim hHP hcm hdom
  · exact no_dominant_original_segre_second_ruling_cross_relation H hd hH hrank hind I hSegre
      hN hH0 G hG c hGh P hm hP hprim hHP hcm hdom

/-- Lemma 5.2: in the paper's Segre coordinates the actual dominant
primitive restriction preserves neither rational ruling parameter.
All local and differential data are conclusions of the original hypotheses. -/
theorem lemma_5_2
    (hN : IsNilpotent (jac H)) (hH0 : H ≠ 0)
    (G : R₀) (hG : G ≠ 0) (c : ℕ) (hGh : G.IsHomogeneous c)
    (P : Fin 4 → R₀) {m : ℕ} (hm : 0 < m) (hP : IsHomogMap P m)
    (hprim : IsPrimitiveVec P) (hHP : H = fun i => G * P i) (hcm : c + m = d)
    (hdom : originalProjectiveRestrictionDominant H hd hH hH0 hrank I P hm hP hprim) :
    let σ := segreProjectiveDominantConeRestriction H hd hH hrank hind I hSegre hH0 P hm hP hprim hdom
    let ρ := algebraMap R₀ (Q₀).asIdeal.ResidueField
    (σ (ρ (X 2) / ρ (X 0)) ≠ ρ (X 2) / ρ (X 0)) ∧
      (σ (ρ (X 1) / ρ (X 0)) ≠ ρ (X 1) / ρ (X 0)) := by
  dsimp only
  constructor
  · exact no_dominant_original_segre_first_ruling_preserving_restriction H hd hH hrank hind I hSegre
      hN hH0 G hG c hGh P hm hP hprim hHP hcm hdom
  · intro hpres
    have hx : algebraMap R₀ (Q₀).asIdeal.ResidueField (X 0) ≠ 0 := by
      rw [Ne, Ideal.algebraMap_residueField_eq_zero]
      exact segre_original_source_first_coordinate_not_mem_determinant_prime H hd hH hrank hind I hSegre
    obtain ⟨_, hc⟩ := dominant_cone_preserved_quotient_cross_relation (Q₀).asIdeal
      (standardRulingPolynomial (F := K)) rfl P
      (segre_projective_dominance_residue_kernel H hd hH hrank hind I hSegre hH0 P hm hP hprim hdom)
      (X 1) (X 0) hx hpres
    apply no_dominant_original_segre_second_ruling_cross_relation H hd hH hrank hind I hSegre
      hN hH0 G hG c hGh P hm hP hprim hHP hcm hdom
    apply Ideal.mem_span_singleton.mpr
    simpa only [aeval_X, mul_comm (X 1) (P 0)] using hc

end DimensionFourDependence
