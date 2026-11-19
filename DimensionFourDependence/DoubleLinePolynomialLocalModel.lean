import DimensionFourDependence.RationalPointLocalModel
import DimensionFourDependence.SimpleRootLocalIntersection

/-! # The actual localized polynomial algebra of a doubled line and a quadric

We form the quotient of F[u,v] by u^2 and the explicit quadratic G,
then localize at the prime of the origin. The preceding rational-point
construction proves its maximal-ideal and residue-field descriptions.
The local intersection bound therefore applies to this actual quotient
localization without any supplied local-ring model conditions.
-/

namespace DimensionFourDependence

open MvPolynomial Module

variable {F : Type*} [Field F]

/-- A quadratic vanishing at the origin, with its linear and quadratic
coefficients in the original two affine coordinates. -/
noncomputable def doubleLineQuadratic (a b c e f : F) : MvPolynomial (Fin 2) F :=
  C a * X 0 + C b * X 1 + C c * X 0 ^ 2 + C e * X 0 * X 1 + C f * X 1 ^ 2

/-- The full intersection ideal of the doubled line and the quadric. -/
noncomputable def doubleLineIntersectionIdeal (a b c e f : F) : Ideal (MvPolynomial (Fin 2) F) :=
  Ideal.span {X 0 ^ 2, doubleLineQuadratic a b c e f}

/-- Both intersection equations vanish at the actual origin. -/
theorem doubleLineIntersectionIdeal_origin (a b c e f : F) :
    doubleLineIntersectionIdeal a b c e f ≤
      RingHom.ker (aeval (fun _ : Fin 2 => (0 : F))).toRingHom := by
  apply Ideal.span_le.mpr
  rintro p (rfl | rfl)
  · change aeval (fun _ : Fin 2 => (0 : F)) (X 0 ^ 2) = 0
    simp
  · change aeval (fun _ : Fin 2 => (0 : F)) (doubleLineQuadratic a b c e f) = 0
    simp [doubleLineQuadratic]

/-- The concrete quotient localization at the origin of the intersection. -/
noncomputable abbrev doubleLineIntersectionLocalRing (a b c e f : F) :=
  Localization.AtPrime (zeroPointQuotientPrime (doubleLineIntersectionIdeal a b c e f)
    (doubleLineIntersectionIdeal_origin a b c e f))

/-- The first original affine coordinate in the local intersection algebra. -/
noncomputable def doubleLineLocalU (a b c e f : F) : doubleLineIntersectionLocalRing a b c e f :=
  zeroPointLocalCoordinate (doubleLineIntersectionIdeal a b c e f)
    (doubleLineIntersectionIdeal_origin a b c e f) 0

/-- The second original affine coordinate in the local intersection algebra. -/
noncomputable def doubleLineLocalV (a b c e f : F) : doubleLineIntersectionLocalRing a b c e f :=
  zeroPointLocalCoordinate (doubleLineIntersectionIdeal a b c e f)
    (doubleLineIntersectionIdeal_origin a b c e f) 1

/-- The specified polynomial presentation map into the actual local algebra. -/
noncomputable def doubleLineLocalPolynomialHom (a b c e f : F) :
    MvPolynomial (Fin 2) F →ₐ[F] doubleLineIntersectionLocalRing a b c e f :=
  (IsScalarTower.toAlgHom F (MvPolynomial (Fin 2) F ⧸ doubleLineIntersectionIdeal a b c e f)
    (doubleLineIntersectionLocalRing a b c e f)).comp
      (Ideal.Quotient.mkₐ F (doubleLineIntersectionIdeal a b c e f))

/-- The presentation map sends each variable to its original local coordinate. -/
theorem doubleLineLocalPolynomialHom_X (a b c e f : F) :
    doubleLineLocalPolynomialHom a b c e f (X 0) = doubleLineLocalU a b c e f ∧
      doubleLineLocalPolynomialHom a b c e f (X 1) = doubleLineLocalV a b c e f := ⟨rfl, rfl⟩

/-- Every original equation in the full intersection ideal is zero
in the actual localized intersection algebra. -/
theorem doubleLineLocalPolynomialHom_relation (a b c e f : F)
    (p : MvPolynomial (Fin 2) F) (hp : p ∈ doubleLineIntersectionIdeal a b c e f) :
    doubleLineLocalPolynomialHom a b c e f p = 0 := by
  change algebraMap (MvPolynomial (Fin 2) F ⧸ doubleLineIntersectionIdeal a b c e f)
    (doubleLineIntersectionLocalRing a b c e f)
      (Ideal.Quotient.mk (doubleLineIntersectionIdeal a b c e f) p) = 0
  rw [Ideal.Quotient.eq_zero_iff_mem.mpr hp, map_zero]

/-- The actual quotient localization has exactly the stated doubled-line
and quadratic relations in its original two coordinate images. -/
theorem doubleLineLocal_equations (a b c e f : F) :
    (doubleLineLocalU a b c e f) ^ 2 = 0 ∧
      algebraMap F (doubleLineIntersectionLocalRing a b c e f) a * doubleLineLocalU a b c e f +
        algebraMap F (doubleLineIntersectionLocalRing a b c e f) b * doubleLineLocalV a b c e f +
        algebraMap F (doubleLineIntersectionLocalRing a b c e f) c * (doubleLineLocalU a b c e f) ^ 2 +
        algebraMap F (doubleLineIntersectionLocalRing a b c e f) e * doubleLineLocalU a b c e f * doubleLineLocalV a b c e f +
        algebraMap F (doubleLineIntersectionLocalRing a b c e f) f * (doubleLineLocalV a b c e f) ^ 2 = 0 := by
  have hu := doubleLineLocalPolynomialHom_relation a b c e f (X 0 ^ 2) (Ideal.subset_span (by simp))
  have hG := doubleLineLocalPolynomialHom_relation a b c e f (doubleLineQuadratic a b c e f)
    (Ideal.subset_span (by simp))
  have hX := doubleLineLocalPolynomialHom_X a b c e f
  constructor
  · simpa only [map_pow, hX.1] using hu
  · simpa only [doubleLineQuadratic, map_add, map_mul, map_pow, hX.1, hX.2,
      show ∀ z : F, doubleLineLocalPolynomialHom a b c e f (C z) =
        algebraMap F (doubleLineIntersectionLocalRing a b c e f) z from
          fun z => (doubleLineLocalPolynomialHom a b c e f).commutes z] using hG

/-- The maximal ideal of the actual quotient localization is generated
by its original two coordinate images. -/
theorem doubleLineLocal_maximalIdeal (a b c e f : F) :
    IsLocalRing.maximalIdeal (doubleLineIntersectionLocalRing a b c e f) =
      Ideal.span ({doubleLineLocalU a b c e f, doubleLineLocalV a b c e f} :
        Set (doubleLineIntersectionLocalRing a b c e f)) := by
  rw [zeroPointLocal_maximalIdeal]
  congr 1
  ext z
  constructor
  · rintro ⟨i, rfl⟩
    fin_cases i <;> simp [doubleLineLocalU, doubleLineLocalV]
  · rintro (rfl | rfl)
    · exact ⟨0, rfl⟩
    · exact ⟨1, rfl⟩

/-- The two original coordinates vanish in the actual local residue field. -/
theorem doubleLineLocal_coordinates_mem_maximalIdeal (a b c e f : F) :
    doubleLineLocalU a b c e f ∈ IsLocalRing.maximalIdeal (doubleLineIntersectionLocalRing a b c e f) ∧
      doubleLineLocalV a b c e f ∈ IsLocalRing.maximalIdeal (doubleLineIntersectionLocalRing a b c e f) := by
  rw [doubleLineLocal_maximalIdeal]
  constructor <;> exact Ideal.subset_span (by simp)

/-- The actual local intersection's residue field is the coefficient field. -/
theorem doubleLineLocal_coefficient_residue_surjective (a b c e f : F) :
    Function.Surjective (algebraMap F (IsLocalRing.ResidueField (doubleLineIntersectionLocalRing a b c e f))) :=
  zeroPointLocal_coefficient_residue_surjective (doubleLineIntersectionIdeal a b c e f)
    (doubleLineIntersectionIdeal_origin a b c e f)

/-- A nonzero linear v coefficient gives the length-two upper bound
for the actual localized polynomial intersection. No local model,
maximal-ideal generators or residue-field identification are assumed. -/
theorem doubleLine_polynomial_local_intersection_dimension_and_length_le_two
    (a b c e f : F) (hb : b ≠ 0) :
    Module.Finite F (doubleLineIntersectionLocalRing a b c e f) ∧
      finrank F (doubleLineIntersectionLocalRing a b c e f) ≤ 2 ∧
      Module.length (doubleLineIntersectionLocalRing a b c e f)
        (doubleLineIntersectionLocalRing a b c e f) ≤ 2 := by
  have hmem := doubleLineLocal_coordinates_mem_maximalIdeal a b c e f
  have heq := doubleLineLocal_equations a b c e f
  exact simple_root_double_line_local_dimension_and_length_le_two
    (doubleLineLocalU a b c e f) (doubleLineLocalV a b c e f) hmem.1 hmem.2 a b c e f hb heq.1 heq.2
    (doubleLineLocal_maximalIdeal a b c e f) (doubleLineLocal_coefficient_residue_surjective a b c e f)

end DimensionFourDependence
