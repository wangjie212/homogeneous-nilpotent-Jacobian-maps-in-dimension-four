import DimensionFourDependence.ConeGaussTangentDifferential
import DimensionFourDependence.RationalParameterConstants

/-! # The original cone parameter differential has the actual ruling kernel

The original normalized normal has constant pivot one and a nonzero
first derivative. The tangent differential identity therefore forces
its second-normal pairing to be nonzero and identifies the kernel.
-/

namespace DimensionFourDependence

open Matrix MvPolynomial

section LinearAlgebra

variable {F : Type*} [Field F] {n : ℕ}

/-- A constant pivot and a genuine ruling covector force the scalar
in the tangent differential identity to be nonzero. Its kernel is
then exactly the ruling kernel on the tangent hyperplane. -/
theorem tangent_differential_scalar_ne_zero_and_kernel
    (r b c : Fin n → F) (a : Fin n) (hra : r a ≠ 0) (hca : c a = 0) (hc : c ≠ 0)
    (s : F) (hidentity : ∀ v : Fin n → F, r ⬝ᵥ v = 0 → s * (b ⬝ᵥ v) + c ⬝ᵥ v = 0) :
    s ≠ 0 ∧ ∀ v : Fin n → F, r ⬝ᵥ v = 0 → (b ⬝ᵥ v = 0 ↔ c ⬝ᵥ v = 0) := by
  classical
  have hs : s ≠ 0 := by
    intro hz
    apply hc
    funext i
    let v : Fin n → F := Pi.single i 1 - (r i / r a) • Pi.single a 1
    have hrv : r ⬝ᵥ v = 0 := by
      simp only [v, dotProduct_sub, dotProduct_smul, dotProduct_single, mul_one, smul_eq_mul]
      exact sub_eq_zero.mpr (div_mul_cancel₀ _ hra).symm
    have he := hidentity v hrv
    simpa [hz, v, dotProduct_sub, dotProduct_smul, dotProduct_single, hca] using he
  refine ⟨hs, fun v hv => ?_⟩
  have he := hidentity v hv
  constructor
  · intro hb
    simpa only [hb, mul_zero, zero_add] using he
  · intro hc₀
    rw [hc₀, add_zero] at he
    exact (mul_eq_zero.mp he).resolve_left hs

end LinearAlgebra

universe u

variable {K : Type u} [Field K] [CharZero K]

/-- In the original rational Gauss parameter, the normalized normal
has nonzero first derivative for every actual nonplanar homogeneous map. -/
theorem original_gauss_normal_parameter_derivative_ne_zero
    (H : Fin 4 → MvPolynomial (Fin 4) K) {d : ℕ} (hd : 0 < d) (hH : IsHomogMap H d)
    (hind : ¬ ComponentsDependent H) (I : ImageRelationWitness H)
    (e : RatFunc K ≃ₐ[K] projectiveRatioField (K := K)
      (rationalImageNormal H I.equation) (imageNormalPivot H I)) :
    (fun i => rationalParameterDerivative K (gaussParameterNormal H I e i)) ≠ 0 := by
  intro hz
  have hscalar (i : Fin 4) : ∃ c : K, gaussParameterNormal H I e i = algebraMap K (RatFunc K) c :=
    (rationalParameterDerivative_eq_zero_iff_scalar _).mp (congrFun hz i)
  choose c hc using hscalar
  exact hind (I.dependent_of_affine_rational_gauss_parameter H hd hH e 0 (fun _ => 0) c
    (fun i => by
      change gaussParameterNormal H I e i = _
      simpa only [map_zero, zero_mul, zero_add] using hc i))

/-- The actual original cone parameter differential has exactly the
kernel of the first parameter-normal derivative on the actual cone
tangent hyperplane. The second-normal denominator is proved nonzero;
neither a nonzero differential nor a ruling-kernel assumption is supplied. -/
theorem original_cone_gauss_parameter_has_ruling_kernel
    (H : Fin 4 → MvPolynomial (Fin 4) K) {d : ℕ} (hd : 0 < d) (hH : IsHomogMap H d)
    (hind : ¬ ComponentsDependent H) (hrank : polyRank (jac H) = 3) (I : ImageRelationWitness H)
    (e : RatFunc K ≃ₐ[K] projectiveRatioField (K := K)
      (rationalImageNormal H I.equation) (imageNormalPivot H I))
    (p q : MvPolynomial (Fin 4) K)
    (ht : imageConeGaussHom H I e RatFunc.X =
      algebraMap (MvPolynomial (Fin 4) K) (imageRelationIdeal H).ResidueField p /
        algebraMap (MvPolynomial (Fin 4) K) (imageRelationIdeal H).ResidueField q) :
    ((fun i => imageConeGaussHom H I e
        (rationalParameterDerivative K (rationalParameterDerivative K (gaussParameterNormal H I e i)))) ⬝ᵥ
      (fun i => algebraMap (MvPolynomial (Fin 4) K) (imageRelationIdeal H).ResidueField (X i))) ≠ 0 ∧
      ∀ v : Fin 4 → (imageRelationIdeal H).ResidueField,
        mappedPolynomialGradient
          (algebraMap (MvPolynomial (Fin 4) K) (imageRelationIdeal H).ResidueField) I.equation ⬝ᵥ v = 0 →
        (polynomialRatioCovector
          (algebraMap (MvPolynomial (Fin 4) K) (imageRelationIdeal H).ResidueField) p q ⬝ᵥ v = 0 ↔
          (fun i => imageConeGaussHom H I e (rationalParameterDerivative K (gaussParameterNormal H I e i))) ⬝ᵥ v = 0) := by
  let φ := imageConeGaussHom H I e
  let ν := gaussParameterNormal H I e
  let a := imageNormalPivot H I
  have hνa : ν a = 1 := by
    apply φ.injective
    change imageConeGaussHom H I e (gaussParameterNormal H I e (imageNormalPivot H I)) = φ 1
    rw [imageConeGaussHom_normal, div_self (image_cone_normal_pivot_ne_zero H I), map_one]
  have hca : φ (rationalParameterDerivative K (ν a)) = 0 := by rw [hνa, Derivation.map_one_eq_zero, map_zero]
  have hc : (fun i => φ (rationalParameterDerivative K (ν i))) ≠ 0 := by
    intro hz
    apply original_gauss_normal_parameter_derivative_ne_zero H hd hH hind I e
    funext i
    apply φ.injective
    change φ (rationalParameterDerivative K (ν i)) = φ 0
    rw [map_zero]
    exact congrFun hz i
  exact tangent_differential_scalar_ne_zero_and_kernel _ _ _ a (image_cone_normal_pivot_ne_zero H I)
    hca hc _ (fun v hv => original_cone_gauss_parameter_tangent_differential_identity H hd hH hrank I e p q ht v hv)

end DimensionFourDependence
