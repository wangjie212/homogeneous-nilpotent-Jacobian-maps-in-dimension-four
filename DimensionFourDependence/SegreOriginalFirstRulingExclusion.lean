import DimensionFourDependence.SegreDominanceWronskian
import DimensionFourDependence.Lemma43ConeRestriction

/-! # Lemma 5.2 for the first ruling, in the original source divisor -/

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
local notation "O₀" => Localization.AtPrime (Q₀).asIdeal
local notation "κ₀" => (Q₀).asIdeal.ResidueField
local notation "F₀" => FractionRing R₀
local notation "Φ₀" => primeLocalizationFractionHom (F := F₀) (Q₀).asIdeal

/-- The first ruling cannot be preserved by a dominant primitive
restriction of the original nilpotent homogeneous Segre map. All
divisor coordinates, local derivatives, determinant order, normalized
units, residue operators, Euler weights and the Wronskian are constructed. -/
theorem no_dominant_original_segre_first_ruling_cross_relation
    (hN : IsNilpotent (jac H)) (hH0 : H ≠ 0)
    (G : R₀) (hG : G ≠ 0) (c : ℕ) (hGh : G.IsHomogeneous c)
    (P : Fin 4 → R₀) {m : ℕ} (hm : 0 < m) (hP : IsHomogMap P m)
    (hprim : IsPrimitiveVec P) (hHP : H = fun i => G * P i) (hcm : c + m = d)
    (hdom : originalProjectiveRestrictionDominant H hd hH hH0 hrank I P hm hP hprim)
    (hcross : P 2 * X 0 - P 0 * X 2 ∈ (Q₀).asIdeal) : False := by
  obtain ⟨x, y, π, t, z, s, D, hx, hy, hπ, ht, hz, hs, hmax, hD⟩ :=
    segre_original_source_divisor_constructs_chart_and_derivations H hd hH hrank hind I hSegre
  obtain ⟨j, v, u, p, hp, hfactor, hfirst, hdiv⟩ :=
    segre_dominant_primitive_restriction_constructs_normalized_outputs H hd hH hrank hind I hSegre
      hH0 G hG P hm hP hprim hHP hdom x π hx hπ
  have hpres := segre_original_cross_relation_constructs_residue_preservation H hd hH hrank hind I hSegre
    P hcross t ht v u p hp hfirst
  have hW := segre_projective_dominance_constructs_original_ruling_wronskian H hd hH hrank hind I hSegre
    hH0 P hm hP hprim hdom hcross D hD x y π t hx hy hπ ht hmax v p hp
  have hmEq : m = d - c := by omega
  have hPm : IsHomogMap P (d - c) := hmEq ▸ hP
  exact segre_original_regular_source_ruling_preservation_excluded H hH hN hind I hSegre
    G P c hG hGh hPm hHP (Φ₀).toRingHom
    (segre_original_source_divisor_fraction_map_injective H hd hH hrank hind I hSegre)
    D hD j x y π t z s (fun i => algebraMap R₀ (O₀) (H i)) p hx hy hπ ht hz hs hmax
    (fun i => primeLocalizationFractionHom_algebraMap _ _) hfactor u hfirst hpres hdiv hW

/-- The exact cone residue substitution kernel supplied by actual
projective dominance, retaining the original determinant prime. -/
theorem segre_projective_dominance_residue_kernel
    (hH0 : H ≠ 0) (P : Fin 4 → R₀) {m : ℕ} (hm : 0 < m)
    (hP : IsHomogMap P m) (hprim : IsPrimitiveVec P)
    (hdom : originalProjectiveRestrictionDominant H hd hH hH0 hrank I P hm hP hprim)
    (z : R₀) : algebraMap R₀ κ₀ (aeval P z) = 0 ↔ z ∈ (Q₀).asIdeal := by
  rw [Ideal.algebraMap_residueField_eq_zero]
  exact segre_projective_restriction_dominance_constructs_kernel H hd hH hrank hind I hSegre hH0 P hm hP hprim hdom z

/-- Actual projective dominance induces the corresponding endomorphism
of the original quadric cone function field. -/
noncomputable def segreProjectiveDominantConeRestriction
    (hH0 : H ≠ 0) (P : Fin 4 → R₀) {m : ℕ} (hm : 0 < m)
    (hP : IsHomogMap P m) (hprim : IsPrimitiveVec P)
    (hdom : originalProjectiveRestrictionDominant H hd hH hH0 hrank I P hm hP hprim) :
    κ₀ →ₐ[K] κ₀ := dominantConeRestriction (Q₀).asIdeal P
      (segre_projective_dominance_residue_kernel H hd hH hrank hind I hSegre hH0 P hm hP hprim hdom)

/-- Lemma 5.2 for the first Segre ruling, expressed by preservation of
its actual original rational parameter in the cone function field.
There are no supplied local-ring or differential hypotheses. -/
theorem no_dominant_original_segre_first_ruling_preserving_restriction
    (hN : IsNilpotent (jac H)) (hH0 : H ≠ 0)
    (G : R₀) (hG : G ≠ 0) (c : ℕ) (hGh : G.IsHomogeneous c)
    (P : Fin 4 → R₀) {m : ℕ} (hm : 0 < m) (hP : IsHomogMap P m)
    (hprim : IsPrimitiveVec P) (hHP : H = fun i => G * P i) (hcm : c + m = d)
    (hdom : originalProjectiveRestrictionDominant H hd hH hH0 hrank I P hm hP hprim)
    (hpres : segreProjectiveDominantConeRestriction H hd hH hrank hind I hSegre hH0 P hm hP hprim hdom
      (algebraMap R₀ κ₀ (X 2) / algebraMap R₀ κ₀ (X 0)) =
        algebraMap R₀ κ₀ (X 2) / algebraMap R₀ κ₀ (X 0)) : False := by
  have hx : algebraMap R₀ κ₀ (X 0) ≠ 0 := by
    rw [Ne, Ideal.algebraMap_residueField_eq_zero]
    exact segre_original_source_first_coordinate_not_mem_determinant_prime H hd hH hrank hind I hSegre
  obtain ⟨_, hc⟩ := dominant_cone_preserved_quotient_cross_relation (Q₀).asIdeal
    (standardRulingPolynomial (F := K)) rfl P
    (segre_projective_dominance_residue_kernel H hd hH hrank hind I hSegre hH0 P hm hP hprim hdom)
    (X 2) (X 0) hx hpres
  apply no_dominant_original_segre_first_ruling_cross_relation H hd hH hrank hind I hSegre
    hN hH0 G hG c hGh P hm hP hprim hHP hcm hdom
  apply Ideal.mem_span_singleton.mpr
  simpa only [aeval_X, mul_comm (X 2) (P 0)] using hc

end DimensionFourDependence
