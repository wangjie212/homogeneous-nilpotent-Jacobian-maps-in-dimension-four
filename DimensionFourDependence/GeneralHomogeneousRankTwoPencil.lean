import DimensionFourDependence.GeneralHomogeneousProjectiveField
import DimensionFourDependence.GeneralRationalSourceCurveField
import DimensionFourDependence.HomogeneousRankTwoPolynomialPencil

/-! # Actual homogeneous rank-two source pencils in arbitrary finite dimension -/

namespace DimensionFourDependence

open MvPolynomial Matrix

universe u
set_option maxHeartbeats 5000000

variable {K : Type u} [Field K] [CharZero K] {n : ℕ}
local notation "R₀" => MvPolynomial (Fin n) K
local notation "F₀" => FractionRing (MvPolynomial (Fin n) K)

theorem general_homogeneous_rank_two_projective_ratio_field_rational
    (H : Fin n → R₀) {d : ℕ} (hd : 0 < d) (hH : IsHomogMap H d)
    (hrank : polyRank (jac H) = 2) (a : Fin n) (ha : H a ≠ 0) :
    Nonempty (RatFunc K ≃ₐ[K] projectiveRatioField (K := K)
      (fun i => algebraMap R₀ F₀ (H i)) a) :=
  general_source_curve_field_rational
    (fun i => algebraMap R₀ F₀ (H i) / algebraMap R₀ F₀ (H a))
    (general_homogeneous_rank_two_projective_ratio_field_trdeg_one H hd hH hrank a ha)

/-- The actual rank-two map constructs a primitive polynomial
parameter vector, its nonzero source scalar, and a reduced homogeneous
source pencil for the same transcendental parameter. No parametrization,
source pencil or function-field embedding is supplied. -/
theorem general_homogeneous_rank_two_map_constructs_primitive_projective_parameter_and_source_pencil
    (H : Fin n → R₀) {d : ℕ} (hd : 0 < d) (hH : IsHomogMap H d)
    (hrank : polyRank (jac H) = 2) (a : Fin n) (ha : H a ≠ 0) :
    ∃ φ : RatFunc K →ₐ[K] F₀,
      φ.fieldRange = projectiveRatioField (K := K) (fun i => algebraMap R₀ F₀ (H i)) a ∧
      Transcendental K (φ RatFunc.X) ∧ sourceEuler (K := K) (φ RatFunc.X) = 0 ∧
      ∃ (p q : R₀) (D : ℕ), 0 < D ∧ p ≠ 0 ∧ q ≠ 0 ∧
        p.IsHomogeneous D ∧ q.IsHomogeneous D ∧ IsRelPrime p q ∧
        φ RatFunc.X = algebraMap R₀ F₀ p / algebraMap R₀ F₀ q ∧
        ∃ (v : Fin n → Polynomial K) (r : F₀), v ≠ 0 ∧
          (∀ f : Polynomial K, (∀ i, f ∣ v i) → IsUnit f) ∧ r ≠ 0 ∧
          ∀ i, algebraMap R₀ F₀ (H i) = r * Polynomial.aeval (φ RatFunc.X) (v i) := by
  let U : Fin n → F₀ := fun i => algebraMap R₀ F₀ (H i)
  let M := projectiveRatioField (K := K) U a
  have hUa : U a ≠ 0 := by
    exact fun hz => ha (IsFractionRing.injective R₀ F₀ (hz.trans (map_zero _).symm))
  obtain ⟨e⟩ := general_homogeneous_rank_two_projective_ratio_field_rational H hd hH hrank a ha
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
    have hM := general_projective_ratio_field_common_weight_constants
      (sourceEuler (K := K)) U a (d : F₀) (fun i => sourceEuler_homogeneous (H i) (hH i))
    exact hM (e RatFunc.X).property
  obtain ⟨p, q, D, hD, hp, hq, hpH, hqH, hrel, hparameter⟩ :=
    sourceEuler_constant_reduced_homogeneous_fraction (φ RatFunc.X) ht hEuler
  let x : Fin n → M := fullOutputCoordinate (K := K) (fun i => U i / U a)
  let b : Fin n → RatFunc K := fun i => e.symm (x i)
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
  have hcoord (i : Fin n) : φ (b i) = U i / U a := by
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

variable [IsAlgClosed K]

theorem general_homogeneous_rank_two_map_constructs_primitive_polynomial_binary_pencil_factorization
    (H : Fin n → R₀) {d : ℕ} (hd : 0 < d) (hH : IsHomogMap H d)
    (hrank : polyRank (jac H) = 2) :
    ∃ (p q g : R₀) (D N c : ℕ) (v : Fin n → Polynomial K),
      0 < D ∧ 0 < N ∧ p ≠ 0 ∧ q ≠ 0 ∧ g ≠ 0 ∧
      p.IsHomogeneous D ∧ q.IsHomogeneous D ∧ g.IsHomogeneous c ∧
      c + D * N = d ∧ IsRelPrime p q ∧
      (∀ i, (v i).natDegree ≤ N) ∧ (∃ i, (v i).coeff N ≠ 0) ∧
      (∀ f : Polynomial K, (∀ i, f ∣ v i) → IsUnit f) ∧
      IsPrimitiveVec (fun i => homogeneousParameterPolynomialValue (v i) N p q) ∧
      (∀ i, ((v i).homogenize N).IsHomogeneous N) ∧
      ∀ i, H i = g * aeval ![p, q] ((v i).homogenize N) := by
  classical
  have hH0 : H ≠ 0 := by
    intro hz
    have hJ0 : jac H = 0 := by
      funext i j
      simp [hz, jac]
    have hr0 : polyRank (jac H) = 0 := by rw [hJ0]; simp [polyRank]
    omega
  obtain ⟨a, ha⟩ : ∃ a, H a ≠ 0 := by
    simpa only [ne_eq, _root_.funext_iff, Pi.zero_apply, not_forall] using hH0
  obtain ⟨φ, _hφ, ht, _hEuler, p, q, D, hD, hp, hq, hpH, hqH, hrel, htfrac,
    v, r, hv, hvprim, hr, hrep⟩ :=
    general_homogeneous_rank_two_map_constructs_primitive_projective_parameter_and_source_pencil H hd hH hrank a ha
  have ht' : Transcendental K (algebraMap R₀ (FractionRing R₀) p / algebraMap R₀ (FractionRing R₀) q) :=
    htfrac ▸ ht
  have hrep' : ∀ i, algebraMap R₀ (FractionRing R₀) (H i) =
      r * Polynomial.aeval (algebraMap R₀ (FractionRing R₀) p / algebraMap R₀ (FractionRing R₀) q) (v i) := by
    simpa only [htfrac] using hrep
  obtain ⟨N, g, hN, htop, hg, hprim, hWne, hfactor⟩ :=
    projective_parameter_representation_constructs_primitive_source_polynomial_factorization
      H p q hq hrel v hv hvprim r hr ht' hrep'
  let W : Fin n → R₀ := fun i => homogeneousParameterPolynomialValue (v i) N p q
  have hWhom (i) : (W i).IsHomogeneous (D * N) :=
    homogeneous_parameter_value_source_homogeneous (v i) N p q hpH hqH
  have hNpos : 0 < N := by
    by_contra hn
    have hN0 : N = 0 := by omega
    have hWconst (i) : W i = C ((W i).coeff 0) :=
      eq_C_of_isHomogeneous_zero (by simpa only [hN0, mul_zero] using hWhom i)
    have hconst : H = fun i => g * C ((W i).coeff 0) := by
      funext i
      exact (hfactor i).trans (congrArg (g * ·) (hWconst i))
    have hle := polynomial_scalar_constant_vector_jacobian_rank_at_most_one g (fun i => (W i).coeff 0)
    rw [← hconst, hrank] at hle
    omega
  obtain ⟨j, hj⟩ : ∃ j, W j ≠ 0 := by
    simpa only [ne_eq, _root_.funext_iff, Pi.zero_apply, not_forall] using hWne
  have hprod : g * W j ≠ 0 := mul_ne_zero hg hj
  obtain ⟨c, hgc⟩ := isHomogeneous_of_mul_left
    (p := g) (q := W j) (by rw [← hfactor j]; exact hH j) hprod
  have hdegree : c + D * N = d := (hgc.mul (hWhom j)).inj_right
    (by rw [← hfactor j]; exact hH j) hprod
  exact ⟨p, q, g, D, N, c, v, hD, hNpos, hp, hq, hg, hpH, hqH, hgc,
    hdegree, hrel, hN, htop, hvprim, hprim,
    (fun i => Polynomial.isHomogeneous_homogenize (v i)), hfactor⟩

end DimensionFourDependence
