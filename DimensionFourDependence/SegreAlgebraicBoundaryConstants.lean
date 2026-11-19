import DimensionFourDependence.SegreFiniteProjectiveRulingPoint
import DimensionFourDependence.ActualInfinityPrimeAlgebraicity

/-! # Actual finite Segre boundary points retain algebraic geometric constants -/

namespace DimensionFourDependence

open MvPolynomial
attribute [local instance] MvPolynomial.gradedAlgebra

universe u
set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 100000

variable {K E : Type u} [Field K] [Field E] [Algebra K E]

/-- A finite ruling branch has an actual normalized coordinate field
algebraic over the original geometric constants. Its normalized four
coordinates remain algebraic over the smaller original ruling field. -/
theorem finite_segre_ruling_boundary_normalized_field_isAlgebraic
    (Y : Fin 4 → E) (j : Fin 3)
    (p : ProjectiveSpectrum (homogeneousSubmodule (Option (Fin 4)) E))
    (hinfty : X none ∈ p.asHomogeneousIdeal)
    (hfinite : SegreFiniteRulingBoundaryPoint K Y j p) :
    ∃ a : Fin 4, X (some a) ∉ p.asHomogeneousIdeal ∧
      Algebra.IsAlgebraic E (projectivePrimeRatioField p (some a)) ∧
      ∀ i : Fin 4, IsAlgebraic (segreProjectiveRulingParameterField K Y j p a)
        (projectivePrimeRatioCoordinate p (some a) (some i)) := by
  obtain ⟨a, ha, B, hB, hmem⟩ := hfinite
  let κ := projectivePrimeRatioField p (some a)
  let J := segreProjectiveRulingParameterField K Y j p a
  let : Module.Finite J B := hB
  have halg (i : Fin 4) : IsAlgebraic J (projectivePrimeRatioCoordinate p (some a) (some i)) :=
    (IsAlgebraic.of_finite (R := J)
      (⟨projectivePrimeRatioCoordinate p (some a) (some i), hmem i⟩ : B)).algHom
        (IsScalarTower.toAlgHom J B κ)
  have hJ : J ≤ (IsScalarTower.toAlgHom K E κ).fieldRange := by
    apply IntermediateField.adjoin_le_iff.mpr
    intro x hx
    rw [Set.mem_singleton_iff] at hx
    subst x
    exact ⟨Y j.castSucc / Y 0, rfl⟩
  refine ⟨a, ha, ?_, halg⟩
  apply projectivePrimeRatioField_isAlgebraic_of_coordinates p (some a)
  intro i
  cases i with
  | none =>
    rw [projectivePrimeRatioCoordinate_zero_of_mem p (some a) none hinfty]
    exact isAlgebraic_zero
  | some i =>
    exact isAlgebraic_of_subfield_le_coefficient_image J hJ _ (halg i)

/-- An algebraic extension of the actual full output field preserves
the original rank-three absolute transcendence degree. -/
theorem rank_three_output_algebraic_extension_absolute_trdeg [CharZero K]
    (H : Fin 4 → MvPolynomial (Fin 4) K) (hrank : polyRank (jac H) = 3)
    [Algebra (polynomialOutputField H) E] [IsScalarTower K (polynomialOutputField H) E]
    [Algebra.IsAlgebraic (polynomialOutputField H) E] :
    Algebra.trdeg K E = 3 := by
  let : FaithfulSMul K (polynomialOutputField H) :=
    (faithfulSMul_iff_algebraMap_injective _ _).mpr (algebraMap K (polynomialOutputField H)).injective
  let : FaithfulSMul (polynomialOutputField H) E :=
    (faithfulSMul_iff_algebraMap_injective _ _).mpr (algebraMap (polynomialOutputField H) E).injective
  have he := trdeg_add_eq (A := E) K (polynomialOutputField H)
  rw [show Algebra.trdeg (polynomialOutputField H) E = 0 from trdeg_eq_zero, add_zero,
    polynomialOutputField_trdeg_eq_rank, hrank] at he
  norm_num at he ⊢
  exact he.symm

/-- The normalized coordinate field of the actual finite boundary
branch has dimension three over the original constants, with the
original smaller ruling-parameter algebraicity retained. -/
theorem finite_segre_ruling_boundary_normalized_field_absolute_trdeg
    (Y : Fin 4 → E) (j : Fin 3) (htr : Algebra.trdeg K E = 3)
    (p : ProjectiveSpectrum (homogeneousSubmodule (Option (Fin 4)) E))
    (hinfty : X none ∈ p.asHomogeneousIdeal)
    (hfinite : SegreFiniteRulingBoundaryPoint K Y j p) :
    ∃ a : Fin 4, X (some a) ∉ p.asHomogeneousIdeal ∧
      Algebra.IsAlgebraic E (projectivePrimeRatioField p (some a)) ∧
      Algebra.trdeg K (projectivePrimeRatioField p (some a)) = 3 ∧
      ∀ i : Fin 4, IsAlgebraic (segreProjectiveRulingParameterField K Y j p a)
        (projectivePrimeRatioCoordinate p (some a) (some i)) := by
  obtain ⟨a, ha, halg, hcoords⟩ := finite_segre_ruling_boundary_normalized_field_isAlgebraic
    Y j p hinfty hfinite
  let : Algebra.IsAlgebraic E (projectivePrimeRatioField p (some a)) := halg
  let : FaithfulSMul K E :=
    (faithfulSMul_iff_algebraMap_injective _ _).mpr (algebraMap K E).injective
  let : FaithfulSMul E (projectivePrimeRatioField p (some a)) :=
    (faithfulSMul_iff_algebraMap_injective _ _).mpr (algebraMap E (projectivePrimeRatioField p (some a))).injective
  have he := trdeg_add_eq (A := projectivePrimeRatioField p (some a)) K E
  rw [show Algebra.trdeg E (projectivePrimeRatioField p (some a)) = 0 from trdeg_eq_zero,
    add_zero, htr] at he
  exact ⟨a, ha, halg, he.symm, hcoords⟩

end DimensionFourDependence
