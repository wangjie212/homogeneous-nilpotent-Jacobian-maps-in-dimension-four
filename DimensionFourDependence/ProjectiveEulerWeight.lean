import DimensionFourDependence.GaussImageDimension
import DimensionFourDependence.SourceEuler
import DimensionFourDependence.ConstantField

/-! # The positive Euler weight separates affine outputs from projective ratios

A common Euler weight cancels in every actual output ratio. The ratio
field therefore consists of constants of the source Euler derivation.
A nonzero output of positive degree has nonzero Euler derivative, so
it is transcendental over that actual projective ratio field.
-/

namespace DimensionFourDependence

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

/-- A derivation with a common coordinate weight annihilates the entire
actual projective ratio field, including its rational combinations. -/
theorem projectiveRatioField_le_derivationConstants_of_weight
    (D : Derivation K F F) (Y : Fin 4 → F) (a : Fin 4) (w : F)
    (hY : ∀ i, D (Y i) = w * Y i) :
    projectiveRatioField (K := K) Y a ≤ derivationConstants D := by
  apply IntermediateField.adjoin_le_iff.mpr
  rintro _ ⟨i, rfl⟩
  change D (Y i / Y a) = 0
  rw [D.leibniz_div, hY i, hY a]
  simp only [smul_eq_mul]
  ring

variable [CharZero K]

/-- A nonzero element with nonzero derivation weight is transcendental
over every intermediate subfield annihilated by that derivation. -/
theorem nonzero_weight_transcendental_over_constant_subfield
    (D : Derivation K F F) (R : IntermediateField K F) (hR : R ≤ derivationConstants D)
    (x w : F) (hx : x ≠ 0) (hw : w ≠ 0) (hDx : D x = w * x) :
    Transcendental R x := by
  let : CharZero R := charZero_of_injective_algebraMap (algebraMap K R).injective
  intro halg
  have hz := derivation_zero_of_isAlgebraic (derivationOverConstantSubfield D R hR) x halg
  change D x = 0 at hz
  rw [hDx] at hz
  exact mul_ne_zero hw hx hz

omit [Field F] [Algebra K F] in
/-- Every actual nonzero output of positive homogeneous degree is
transcendental over the actual original-field projective output ratios. -/
theorem homogeneous_output_transcendental_over_projective_ratios
    (H : Fin 4 → MvPolynomial (Fin 4) K) {d : ℕ} (hd : 0 < d) (hH : IsHomogMap H d)
    (a : Fin 4) (ha : H a ≠ 0) :
    Transcendental (projectiveRatioField (K := K)
      (fun i => algebraMap (MvPolynomial (Fin 4) K) (FractionRing (MvPolynomial (Fin 4) K)) (H i)) a)
      (algebraMap (MvPolynomial (Fin 4) K) (FractionRing (MvPolynomial (Fin 4) K)) (H a)) := by
  let Y : Fin 4 → FractionRing (MvPolynomial (Fin 4) K) :=
    fun i => algebraMap (MvPolynomial (Fin 4) K) _ (H i)
  have hw : (d : FractionRing (MvPolynomial (Fin 4) K)) ≠ 0 := by exact_mod_cast hd.ne'
  have hY : ∀ i, sourceEuler (K := K) (Y i) = (d : FractionRing (MvPolynomial (Fin 4) K)) * Y i :=
    fun i => sourceEuler_homogeneous (H i) (hH i)
  have hYa : Y a ≠ 0 := by
    intro hz
    apply ha
    apply IsFractionRing.injective (MvPolynomial (Fin 4) K) (FractionRing (MvPolynomial (Fin 4) K))
    simpa only [map_zero] using hz
  exact nonzero_weight_transcendental_over_constant_subfield (sourceEuler (K := K))
    (projectiveRatioField (K := K) Y a)
    (projectiveRatioField_le_derivationConstants_of_weight _ Y a _ hY) (Y a) _ hYa hw (hY a)

end DimensionFourDependence
