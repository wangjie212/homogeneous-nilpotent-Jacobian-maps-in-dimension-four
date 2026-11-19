import DimensionFourDependence.ProjectiveImageDimension
import DimensionFourDependence.RationalSourceCurveField
import DimensionFourDependence.EulerHomogeneousFractions
import DimensionFourDependence.PrimitiveRationalVector
import DimensionFourDependence.PrimitiveHomogeneousQuasiTranslationRank

/-! # The actual projective image of a homogeneous rank-two map has a rational parameter -/

namespace DimensionFourDependence

open MvPolynomial

universe u
set_option maxHeartbeats 3000000

variable {K : Type u} [Field K] [CharZero K]
local notation "R₀" => MvPolynomial (Fin 4) K
local notation "F₀" => FractionRing (MvPolynomial (Fin 4) K)

/-- The actual projective coordinate field of a positive homogeneous
rank-two map has transcendence degree one. -/
theorem homogeneous_rank_two_projective_ratio_field_trdeg_one
    (H : Fin 4 → R₀) {d : ℕ} (hd : 0 < d) (hH : IsHomogMap H d)
    (hrank : polyRank (jac H) = 2) (a : Fin 4) (ha : H a ≠ 0) :
    Algebra.trdeg K (projectiveRatioField (K := K)
      (fun i => algebraMap R₀ F₀ (H i)) a) = 1 := by
  let M := projectiveRatioField (K := K) (fun i => algebraMap R₀ F₀ (H i)) a
  have he := homogeneous_output_trdeg_eq_projective_add_one H hd hH a ha
  rw [(polynomialOutputField_trdeg_eq_rank H).trans
    (congrArg (fun n : ℕ => (n : Cardinal)) hrank)] at he
  change 2 = Algebra.trdeg K M + 1 at he
  have hle : Algebra.trdeg K M ≤ 2 := (self_le_add_right _ 1).trans_eq he.symm
  obtain ⟨n, hn⟩ := Cardinal.lt_aleph0.mp (hle.trans_lt (by simp))
  rw [hn] at he
  have hn' : 2 = n + 1 := by exact_mod_cast he
  have hn1 : n = 1 := by omega
  change Algebra.trdeg K M = 1
  rw [hn, hn1]
  rfl

/-- Source-line specialization and Lüroth construct the rational
function-field equivalence of the actual projective image curve. -/
theorem homogeneous_rank_two_projective_ratio_field_rational
    (H : Fin 4 → R₀) {d : ℕ} (hd : 0 < d) (hH : IsHomogMap H d)
    (hrank : polyRank (jac H) = 2) (a : Fin 4) (ha : H a ≠ 0) :
    Nonempty (RatFunc K ≃ₐ[K] projectiveRatioField (K := K)
      (fun i => algebraMap R₀ F₀ (H i)) a) :=
  rational_source_curve_field_rational
    (fun i => algebraMap R₀ F₀ (H i) / algebraMap R₀ F₀ (H a))
    (homogeneous_rank_two_projective_ratio_field_trdeg_one H hd hH hrank a ha)

/-- The actual rank-two map constructs a primitive polynomial
parameter vector, its nonzero source scalar, and a reduced homogeneous
source pencil for the same transcendental parameter. No parametrization,
source pencil or function-field embedding is supplied. -/
theorem homogeneous_rank_two_map_constructs_primitive_projective_parameter_and_source_pencil
    (H : Fin 4 → R₀) {d : ℕ} (hd : 0 < d) (hH : IsHomogMap H d)
    (hrank : polyRank (jac H) = 2) (a : Fin 4) (ha : H a ≠ 0) :
    ∃ φ : RatFunc K →ₐ[K] F₀,
      φ.fieldRange = projectiveRatioField (K := K) (fun i => algebraMap R₀ F₀ (H i)) a ∧
      Transcendental K (φ RatFunc.X) ∧ sourceEuler (K := K) (φ RatFunc.X) = 0 ∧
      ∃ (p q : R₀) (D : ℕ), 0 < D ∧ p ≠ 0 ∧ q ≠ 0 ∧
        p.IsHomogeneous D ∧ q.IsHomogeneous D ∧ IsRelPrime p q ∧
        φ RatFunc.X = algebraMap R₀ F₀ p / algebraMap R₀ F₀ q ∧
        ∃ (v : Fin 4 → Polynomial K) (r : F₀), v ≠ 0 ∧
          (∀ f : Polynomial K, (∀ i, f ∣ v i) → IsUnit f) ∧ r ≠ 0 ∧
          ∀ i, algebraMap R₀ F₀ (H i) = r * Polynomial.aeval (φ RatFunc.X) (v i) := by
  let U : Fin 4 → F₀ := fun i => algebraMap R₀ F₀ (H i)
  let M := projectiveRatioField (K := K) U a
  have hUa : U a ≠ 0 := by
    exact fun hz => ha (IsFractionRing.injective R₀ F₀ (hz.trans (map_zero _).symm))
  obtain ⟨e⟩ := homogeneous_rank_two_projective_ratio_field_rational H hd hH hrank a ha
  let φ : RatFunc K →ₐ[K] F₀ := M.val.comp e.toAlgHom
  have hφ : φ.fieldRange = M := by
    ext x
    constructor
    · rintro ⟨z, rfl⟩
      exact (e z).property
    · intro hx
      obtain ⟨z, hz⟩ := e.surjective ⟨x, hx⟩
      exact ⟨z, congrArg Subtype.val hz⟩
  have ht : Transcendental K (φ RatFunc.X) := by
    intro h
    exact RatFunc.transcendental_X ((isAlgebraic_algHom_iff φ φ.injective).mp h)
  have hEuler : sourceEuler (K := K) (φ RatFunc.X) = 0 := by
    have hM := projectiveRatioField_le_derivationConstants_of_weight
      (sourceEuler (K := K)) U a (d : F₀) (fun i => sourceEuler_homogeneous (H i) (hH i))
    exact hM (e RatFunc.X).property
  obtain ⟨p, q, D, hD, hp, hq, hpH, hqH, hrel, hparameter⟩ :=
    sourceEuler_constant_reduced_homogeneous_fraction (φ RatFunc.X) ht hEuler
  let x : Fin 4 → M := fullOutputCoordinate (K := K) (fun i => U i / U a)
  let b : Fin 4 → RatFunc K := fun i => e.symm (x i)
  have hxa : x a = 1 := by
    apply Subtype.ext
    exact div_self hUa
  have hb : b ≠ 0 := by
    intro hz
    have hba : b a = 1 := by
      change e.symm (x a) = 1
      rw [hxa, map_one]
    exact one_ne_zero (hba.symm.trans (congrFun hz a))
  obtain ⟨v, hv, hprim, r, hr, hrep⟩ := rational_vector_primitive_polynomial_presentation b hb
  have hφr : φ r ≠ 0 := by
    intro hz
    exact hr (φ.injective (hz.trans (map_zero φ).symm))
  have hcoord (i : Fin 4) : φ (b i) = U i / U a := by
    change M.val (e (e.symm (x i))) = _
    rw [e.apply_symm_apply]
    rfl
  refine ⟨φ, hφ, ht, hEuler, p, q, D, hD, hp, hq, hpH, hqH, hrel, hparameter,
    v, U a * φ r, hv, hprim, mul_ne_zero hUa hφr, ?_⟩
  intro i
  have he := congrArg φ (hrep i)
  rw [hcoord, map_mul, rational_function_algHom_polynomial_value] at he
  have hi := (div_eq_iff hUa).mp he
  change U i = (U a * φ r) * Polynomial.aeval (φ RatFunc.X) (v i)
  calc
    _ = (φ r * Polynomial.aeval (φ RatFunc.X) (v i)) * U a := hi
    _ = _ := by ring

end DimensionFourDependence
