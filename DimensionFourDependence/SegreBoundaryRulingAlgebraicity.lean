import DimensionFourDependence.SegreRulingRelativeDimension
import DimensionFourDependence.SegreRulingSourceKernel
import DimensionFourDependence.SegreActualBoundaryNonGeneric

/-! # A normalized nongeneric original Segre ruling point is algebraic -/

namespace DimensionFourDependence

open MvPolynomial Matrix
attribute [local instance] coefficientFieldScalarTower MvPolynomial.gradedAlgebra

universe u
set_option maxHeartbeats 3000000
set_option synthInstance.maxHeartbeats 100000
set_option quotPrecheck false

variable {K : Type u} [Field K] [CharZero K]
local notation "S₀" => FractionRing (MvPolynomial (Fin 4) K)

/-- The original ruling field as an actual subfield of a compatible
boundary coefficient extension, with its original parameter embedding. -/
noncomputable def segreBoundaryRulingField
    (Y : Fin 3 → S₀) (hY : AlgebraicIndependent K Y) (j : Fin 3) (hj : j ≠ 0)
    (κ : Type u) [Field κ] [Algebra (coefficientField (K := K) Y) κ]
    [Algebra K κ] [IsScalarTower K (coefficientField (K := K) Y) κ] : IntermediateField K κ :=
  ((IsScalarTower.toAlgHom K (coefficientField (K := K) Y) κ).comp
    (segreRulingFieldCoefficientHom Y hY j hj)).fieldRange

/-- A normalized point on either original Segre ruling has all its
coordinates algebraic over the original ruling field unless it is the
original image generic point. The relative output dimension and the
complete line-density comparison are constructed from the original outputs. -/
theorem nongeneric_normalized_original_segre_ruling_point_isAlgebraic
    (H : Fin 4 → MvPolynomial (Fin 4) K)
    (hY : AlgebraicIndependent K (segreOriginalOutputTriple H))
    {d : ℕ} (hd : 0 < d) (hH : IsHomogMap H d) (hH0 : H ≠ 0)
    (hind : ¬ComponentsDependent H) (hSegre : H 0 * H 3 - H 1 * H 2 = 0)
    (j : Fin 3) (hj : j ≠ 0)
    (κ : Type u) [Field κ] [Algebra (coefficientField (K := K) (segreOriginalOutputTriple H)) κ] [Algebra K κ] [IsScalarTower K (coefficientField (K := K) (segreOriginalOutputTriple H)) κ]
    (b : Fin 4 → κ) (hb : b ≠ 0) (a : Fin 4) (ha : b a = 1)
    (hkernel : (segreRulingMatrix j (segreRulingFieldParameter (segreOriginalOutputTriple H) hY j hj)).map
      ((algebraMap (coefficientField (K := K) (segreOriginalOutputTriple H)) κ).comp (segreRulingFieldCoefficientHom (segreOriginalOutputTriple H) hY j hj).toRingHom) *ᵥ b = 0)
    (hng : projectiveFieldPoint (E := K) b hb ≠ projectiveImageGenericPoint H hd hH hH0) :
    ∀ i, IsAlgebraic (segreBoundaryRulingField (segreOriginalOutputTriple H) hY j hj κ) (b i) := by
  let M := (segreSourceRulingParameterHom (segreOriginalOutputTriple H) hY j hj).fieldRange
  let f : M →ₐ[K] κ := (IsScalarTower.toAlgHom K (coefficientField (K := K) (segreOriginalOutputTriple H)) κ).comp (segreRulingFieldCoefficientHom (segreOriginalOutputTriple H) hY j hj)
  let : Algebra M κ := f.toRingHom.toAlgebra
  let : IsScalarTower K M κ := IsScalarTower.of_algebraMap_eq (fun c => (f.commutes c).symm)
  let A : Matrix (Fin 2) (Fin 4) M := segreRulingMatrix j (segreRulingFieldParameter (segreOriginalOutputTriple H) hY j hj)
  let Q : Fin 4 → S₀ := fun i => algebraMap (MvPolynomial (Fin 4) K) S₀ (H i)
  have hQ0 : Q 0 ≠ 0 := original_segre_first_output_ne_zero H hind
  have hquad : Q 0 * Q 3 - Q 1 * Q 2 = 0 := by
    simpa only [Q, map_sub, map_mul, map_zero] using congrArg (algebraMap (MvPolynomial (Fin 4) K) S₀) hSegre
  have hA : Module.finrank M (LinearMap.ker A.toLin') = 2 := segreRulingMatrix_kernel_finrank _ _
  have hQ : A.map (algebraMap M S₀) *ᵥ Q = 0 :=
    segre_source_output_mem_actual_ruling_field_kernel Q hY hQ0 hquad j hj
  have hdim : Algebra.trdeg M (fullOutputField (K := M) Q) = 2 :=
    segre_ruling_relative_full_output_trdeg_two Q hY hQ0 hquad j hj
  have hbM : A.map (algebraMap M κ) *ᵥ b = 0 := hkernel
  have halg : ∀ i, IsAlgebraic M (b i) := by
    by_contra hn
    apply hng
    apply ProjectiveSpectrum.ext
    apply HomogeneousIdeal.ext'
    intro m R hR
    change R.IsHomogeneous m at hR
    rw [projectiveFieldPoint_homogeneous_mem b hb R hR]
    change aeval b R = 0 ↔ aeval H R = 0
    have he := normalized_kernel_non_algebraic_generic_homogeneous_relations A hA Q hQ hdim b hbM a ha hn
      (MvPolynomial.map (algebraMap K M) R) (hR.map (algebraMap K M))
    rw [aeval_map_algebra_extension, aeval_map_algebra_extension, ← aeval_polynomial_to_fraction] at he
    exact he.trans (map_eq_zero_iff _ (IsFractionRing.injective (MvPolynomial (Fin 4) K) S₀))
  let J := f.fieldRange
  let : Algebra M J := f.equivFieldRange.toAlgHom.toRingHom.toAlgebra
  let : IsScalarTower M J κ := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  intro i
  exact (halg i).tower_top J

end DimensionFourDependence
