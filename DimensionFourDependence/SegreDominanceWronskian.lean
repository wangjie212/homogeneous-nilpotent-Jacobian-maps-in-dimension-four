import DimensionFourDependence.SegreRulingResiduePreservation
import DimensionFourDependence.SegreResidueChartWeights
import DimensionFourDependence.ConeFieldDerivationGeneration
import DimensionFourDependence.DominantQuadricWronskian

/-! # Actual projective dominance constructs the original ruling Wronskian -/

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
local notation "ρ₀" => algebraMap R₀ κ₀
local notation "r₀" => IsLocalRing.residue (O₀)
local notation "D₀" => segreOriginalSourceChartDerivation (K := K)

/-- Dominance of the actual projective primitive restriction and its
polynomial ruling relation construct the nonzero local Wronskian of
every unit-normalized output pair in the original divisor ring. -/
theorem segre_projective_dominance_constructs_original_ruling_wronskian
    (hH0 : H ≠ 0) (P : Fin 4 → R₀) {m : ℕ} (hm : 0 < m)
    (hP : IsHomogMap P m) (hprim : IsPrimitiveVec P)
    (hdom : originalProjectiveRestrictionDominant H hd hH hH0 hrank I P hm hP hprim)
    (hcross : P 2 * X 0 - P 0 * X 2 ∈ (Q₀).asIdeal)
    (D : Fin 4 → Derivation K (O₀) (O₀))
    (hD : ∀ i z, (Φ₀) (D i z) = (D₀) i ((Φ₀) z))
    (x y π t : O₀)
    (hx : (Φ₀) x = rationalCoordinate (K := K) 0)
    (hy : (Φ₀) y = rationalCoordinate (K := K) 1)
    (hπ : (Φ₀) π = segreOriginalSourceUniformizer (K := K))
    (ht : (Φ₀) t = segreOriginalSourceRulingParameter (K := K))
    (hmax : IsLocalRing.maximalIdeal (O₀) = Ideal.span {π})
    (v : (O₀)ˣ) (p : Fin 4 → O₀)
    (hp : ∀ i, p i = (v : O₀) * algebraMap R₀ (O₀) (P i)) :
    (r₀) (p 0) * (r₀) (D 1 (p 1)) - (r₀) (p 1) * (r₀) (D 1 (p 0)) ≠ 0 := by
  letI : CharZero κ₀ := charZero_of_injective_algebraMap (algebraMap K κ₀).injective
  letI : Algebra.EssFiniteType K κ₀ := Algebra.EssFiniteType.comp K R₀ κ₀
  have hφ := segre_original_source_divisor_fraction_map_injective H hd hH hrank hind I hSegre
  obtain ⟨Dx, Dy, hDx, hDy⟩ := segre_regular_source_derivations_construct_residue_operators
    (Φ₀).toRingHom hφ D hD π hπ hmax
  let E : Derivation K κ₀ κ₀ := (r₀) x • Dx + (r₀) y • Dy
  let Y : Fin 4 → κ₀ := fun i => (ρ₀) (P i)
  have hbase : ∀ z : R₀, (r₀) (algebraMap R₀ (O₀) z) = (ρ₀) z := fun z =>
    (IsScalarTower.algebraMap_apply R₀ (O₀) κ₀ z).symm
  have hπκ : (r₀) π = 0 := by
    apply (IsLocalRing.residue_eq_zero_iff π).mpr
    rw [hmax]
    exact Ideal.subset_span (by simp)
  have hxval : x = algebraMap R₀ (O₀) (X 0) := by
    apply hφ
    exact hx.trans (primeLocalizationFractionHom_algebraMap _ _).symm
  have hxκ : (r₀) x ≠ 0 := by
    rw [hxval, hbase, Ne, Ideal.algebraMap_residueField_eq_zero]
    exact segre_original_source_first_coordinate_not_mem_determinant_prime H hd hH hrank hind I hSegre
  have hY0 : Y 0 ≠ 0 := by
    change (ρ₀) (P 0) ≠ 0
    rw [Ne, Ideal.algebraMap_residueField_eq_zero]
    exact segre_dominant_primitive_first_output_not_mem_source_prime H hd hH hrank hind I hSegre hH0 P hm hP hprim hdom
  have hPunit := segre_dominant_primitive_first_output_local_unit H hd hH hrank hind I hSegre hH0 P hm hP hprim hdom
  let u : (O₀)ˣ := hPunit.unit
  have hu : algebraMap R₀ (O₀) (P 0) = (u : O₀) := hPunit.unit_spec.symm
  have hpresq := segre_original_cross_relation_constructs_residue_preservation H hd hH hrank hind I hSegre
    P hcross t ht 1 u (fun i => algebraMap R₀ (O₀) (P i)) (fun i => by simp) hu
  have hpres : Y 2 = (r₀) t * Y 0 := by
    rw [map_mul] at hpresq
    have he := congrArg (fun z : κ₀ => z * (r₀) (u : O₀)) hpresq
    have hc : (r₀) (↑u⁻¹ : O₀) * (r₀) (u : O₀) = 1 := by rw [← map_mul]; simp
    rw [mul_assoc, hc, mul_one] at he
    simpa only [Y, ← hu, hbase] using he
  have hkernel : ∀ z : R₀, (ρ₀) (aeval P z) = 0 ↔ z ∈ (Q₀).asIdeal := by
    intro z
    rw [Ideal.algebraMap_residueField_eq_zero]
    exact segre_projective_restriction_dominance_constructs_kernel H hd hH hrank hind I hSegre hH0 P hm hP hprim hdom z
  let σ := dominantConeRestriction (Q₀).asIdeal P hkernel
  have hσ : ∀ i, σ ((ρ₀) (X i)) = Y i := by
    intro i
    simpa [σ, Y] using dominantConeRestriction_polynomial (Q₀).asIdeal P hkernel (X i)
  have hgen : ∀ L : Derivation K κ₀ κ₀, (∀ i, L (Y i) = 0) → ∀ z, L (σ z) = 0 := by
    intro L hL z
    exact cone_field_derivation_kills_image_of_coordinates (Q₀).asIdeal σ L (fun i => by rw [hσ]; exact hL i) z
  have hquad : Y 0 * Y 3 = Y 1 * Y 2 := by
    have hz := (hkernel (standardRulingPolynomial (F := K))).mpr
      (Ideal.subset_span (by simp))
    simpa [standardRulingPolynomial, Y, sub_eq_zero] using hz
  have hweight : ∀ i, E (Y i) = (m : κ₀) * Y i := by
    intro i
    simpa only [E, Y, ← hbase] using
      segre_original_homogeneous_polynomial_residue_euler_weight (Φ₀).toRingHom hφ D hD
        Dx Dy hDx hDy x y π (algebraMap R₀ (O₀) (P i)) hx hy hπ hπκ
        (P i) (hP i) (primeLocalizationFractionHom_algebraMap _ _)
  obtain ⟨hDyx, hDyy, hDyt, hEx, hEy⟩ :=
    segre_regular_chart_constructs_residue_coordinate_values (Φ₀).toRingHom hφ D hD Dx Dy hDx hDy x y t hx hy ht
  have hW : Y 0 * Dy (Y 1) - Y 1 * Dy (Y 0) ≠ 0 :=
    dominant_quadric_ruling_wronskian_ne_zero σ Y hgen E Dy (m : κ₀) ((r₀) x) ((r₀) y) ((r₀) t)
      (Nat.cast_ne_zero.mpr (Nat.ne_of_gt hm)) hxκ hY0 hweight hEx hEy hDyx hDyy hDyt hpres hquad
  have hv : (r₀) (v : O₀) ≠ 0 := (isUnit_iff_ne_zero.mp (v.isUnit.map (r₀)))
  have he : (r₀) (p 0) * (r₀) (D 1 (p 1)) - (r₀) (p 1) * (r₀) (D 1 (p 0)) =
      ((r₀) (v : O₀)) ^ 2 * (Y 0 * Dy (Y 1) - Y 1 * Dy (Y 0)) := by
    rw [← hDy, ← hDy]
    simp only [hp, map_mul, hbase, Dy.leibniz, smul_eq_mul, Y]
    ring
  rw [he]
  exact mul_ne_zero (pow_ne_zero _ hv) hW

end DimensionFourDependence
