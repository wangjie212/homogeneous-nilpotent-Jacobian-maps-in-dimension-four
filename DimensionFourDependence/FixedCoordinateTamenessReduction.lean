import DimensionFourDependence.FixedCoordinateTranslation
import DimensionFourDependence.LinearTameConjugacy

/-! # Restoring original coordinates and elementary translations in the tameness proof -/

namespace DimensionFourDependence

open Matrix MvPolynomial

set_option maxHeartbeats 2500000

variable {K : Type*} [Field K]

/-- The four-variable homogeneous perturbation reconstructed from the
normalized ternary chart, with the elementary target constants removed. -/
noncomputable def normalizedFixedCoordinateHomogeneousCore
    (B : Fin 3 → MvPolynomial (Fin 4) K) (d : ℕ) :
    Fin 4 → MvPolynomial (Fin 4) K :=
  Fin.lastCases 0 (fun i => lastCoordinateHomogenize (normalizedFixedCoordinateChart B i) d)

/-- A tame factorization of the normalized homogeneous core gives an
actual tame automorphism of the original map, restoring both the
elementary target translation and the original constant coordinates. -/
theorem normalized_fixed_coordinate_core_tameness_restores_original_map
    (H : Fin 4 → MvPolynomial (Fin 4) K)
    (T S : Matrix (Fin 4) (Fin 4) K) (hTS : T * S = 1) (hST : S * T = 1)
    (B : Fin 3 → MvPolynomial (Fin 4) K) {d : ℕ}
    (hG : linearPolynomialConjugate T S H = Fin.lastCases 0 B)
    (hB : ∀ i, (B i).IsHomogeneous d)
    (e : MvPolynomial (Fin 4) K ≃ₐ[K] MvPolynomial (Fin 4) K)
    (het : e ∈ Tame.subgroup K 4)
    (he : ∀ j, e (X j) = X j + normalizedFixedCoordinateHomogeneousCore B d j) :
    ∃ E : MvPolynomial (Fin 4) K ≃ₐ[K] MvPolynomial (Fin 4) K,
      E ∈ Tame.subgroup K 4 ∧ ∀ j, E (X j) = X j + H j := by
  let τ := fixedCoordinateTranslation4 (fixedCoordinateChartConstants B) d
  have heq := automorphism_eq_perturbedPolynomialSubstitution _ e he
  have hcoords (j : Fin 4) :
      (e * τ) (X j) = X j + linearPolynomialConjugate T S H j := by
    have hf := AlgHom.congr_fun (fixed_coordinate_chart_target_translation_factorization B hB) (X j)
    have hes := AlgHom.congr_fun heq (τ (X j))
    change e (τ (X j)) = aeval
      (fun j : Fin 4 => X j + normalizedFixedCoordinateHomogeneousCore B d j) (τ (X j)) at hes
    change e (τ (X j)) = _
    rw [hes, hG]
    simpa only [aeval_X, AlgHom.comp_apply, AlgEquiv.coe_toAlgHom,
      normalizedFixedCoordinateHomogeneousCore] using hf.symm
  exact tame_automorphism_descends_from_constant_linear_conjugacy T S hTS hST H
    (e * τ) hcoords ((Tame.subgroup K 4).mul_mem het
      (fixedCoordinateTranslation4_tame (fixedCoordinateChartConstants B) d))

variable [CharZero K]

/-- Every original homogeneous nilpotent map constructs a normalized
ternary problem over the original field. Proving tame group membership
for its explicit homogeneous core suffices for the original map. No
classification or tameness assertion about that core is assumed here. -/
theorem original_homogeneous_nilpotent_map_constructs_actual_tameness_reduction
    (H : Fin 4 → MvPolynomial (Fin 4) K) {d : ℕ}
    (hd : 0 < d) (hH : IsHomogMap H d) (hN : IsNilpotent (jac H)) :
    ∃ (T S : Matrix (Fin 4) (Fin 4) K)
      (B : Fin 3 → MvPolynomial (Fin 4) K),
      T * S = 1 ∧ S * T = 1 ∧
      linearPolynomialConjugate T S H = Fin.lastCases 0 B ∧
      (∀ i, (B i).IsHomogeneous d) ∧
      (∀ i, (normalizedFixedCoordinateChart B i).totalDegree ≤ d) ∧
      (∀ i, aeval (fun _ : Fin 3 => (0 : K)) (normalizedFixedCoordinateChart B i) = 0) ∧
      IsNilpotent (jac (normalizedFixedCoordinateChart B)) ∧
      ∀ e : MvPolynomial (Fin 4) K ≃ₐ[K] MvPolynomial (Fin 4) K,
        e ∈ Tame.subgroup K 4 →
        (∀ j, e (X j) = X j + normalizedFixedCoordinateHomogeneousCore B d j) →
        ∃ E : MvPolynomial (Fin 4) K ≃ₐ[K] MvPolynomial (Fin 4) K,
          E ∈ Tame.subgroup K 4 ∧ ∀ j, E (X j) = X j + H j := by
  obtain ⟨T, S, B, hTS, hST, hG, hB, hdeg, hnorm, hnil, _hrec⟩ :=
    original_homogeneous_nilpotent_map_constructs_normalized_fixed_coordinate_chart H hd hH hN
  refine ⟨T, S, B, hTS, hST, hG, hB, hdeg, hnorm, hnil, ?_⟩
  intro e het he
  exact normalized_fixed_coordinate_core_tameness_restores_original_map H T S hTS hST B hG hB e het he

end DimensionFourDependence
