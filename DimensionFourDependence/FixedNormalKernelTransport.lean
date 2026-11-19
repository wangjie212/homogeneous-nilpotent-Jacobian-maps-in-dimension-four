import DimensionFourDependence.OriginalConeRulingKernel
import DimensionFourDependence.MatrixKernelScalarExtension

/-! # The original ruling kernel survives a dominant cone restriction

Kernel inclusions extend along every field embedding by matrix
factorization. A restriction fixing the Gauss field fixes the ruling
covector, while its cone normal changes by a nonzero scalar. Hence the
original and substituted parameter differentials have the same tangent
kernel over the entire original cone residue field.
-/

namespace DimensionFourDependence

open Matrix MvPolynomial

section LinearAlgebra

variable {F E : Type*} [Field F] [Field E] {n m r : ℕ}

/-- Matrix-kernel inclusion is preserved by an arbitrary field
homomorphism, without a separately chosen scalar action. -/
theorem matrix_kernel_le_field_map (σ : F →+* E)
    (A : Matrix (Fin m) (Fin n) F) (B : Matrix (Fin r) (Fin n) F)
    (h : LinearMap.ker A.toLin' ≤ LinearMap.ker B.toLin') :
    LinearMap.ker (A.map σ).toLin' ≤ LinearMap.ker (B.map σ).toLin' := by
  obtain ⟨T, hT⟩ := matrix_exists_mul_of_ker_le A B h
  intro v hv
  change A.map σ *ᵥ v = 0 at hv
  change B.map σ *ᵥ v = 0
  rw [hT, Matrix.map_mul, ← Matrix.mulVec_mulVec, hv, Matrix.mulVec_zero]

/-- A field endomorphism preserving the normal line and fixing a
ruling covector transports the actual tangent parameter kernel. It
need not be surjective on the field. -/
theorem fixed_ruling_covector_transports_tangent_kernel
    (σ : F →+* F) (r b c : Fin n → F) (α : F)
    (hr : ∀ i, σ (r i) = α * r i) (hc : ∀ i, σ (c i) = c i)
    (hker : ∀ v : Fin n → F, r ⬝ᵥ v = 0 → (b ⬝ᵥ v = 0 ↔ c ⬝ᵥ v = 0)) :
    ∀ v : Fin n → F, r ⬝ᵥ v = 0 →
      (b ⬝ᵥ v = 0 ↔ (fun i => σ (b i)) ⬝ᵥ v = 0) := by
  have transport (x y : Fin n → F)
      (hxy : ∀ v : Fin n → F, r ⬝ᵥ v = 0 → x ⬝ᵥ v = 0 → y ⬝ᵥ v = 0)
      (v : Fin n → F) (hv : r ⬝ᵥ v = 0) (hx : (fun i => σ (x i)) ⬝ᵥ v = 0) :
      (fun i => σ (y i)) ⬝ᵥ v = 0 := by
    let A : Matrix (Fin 2) (Fin n) F := fun i j => ![r j, x j] i
    let B : Matrix (Fin 1) (Fin n) F := fun _ j => y j
    have hAB : LinearMap.ker A.toLin' ≤ LinearMap.ker B.toLin' := by
      intro w hw
      change A *ᵥ w = 0 at hw
      change B *ᵥ w = 0
      funext i
      exact hxy w (congrFun hw 0) (congrFun hw 1)
    have hAv : A.map σ *ᵥ v = 0 := by
      funext i
      fin_cases i
      · change (fun j => σ (r j)) ⬝ᵥ v = 0
        simp only [hr, dotProduct, mul_assoc, ← Finset.mul_sum]
        change α * (r ⬝ᵥ v) = 0
        rw [hv, mul_zero]
      · exact hx
    exact congrFun (matrix_kernel_le_field_map σ A B hAB hAv) 0
  intro v hv
  constructor
  · intro hb
    have hcv : (fun i => σ (c i)) ⬝ᵥ v = 0 := by
      simpa only [hc] using (hker v hv).mp hb
    exact transport c b (fun w hw => (hker w hw).mpr) v hv hcv
  · intro hσb
    have hσc := transport b c (fun w hw => (hker w hw).mp) v hv hσb
    exact (hker v hv).mpr (by simpa only [hc] using hσc)

end LinearAlgebra

universe u

variable {K : Type u} [Field K] [CharZero K]

/-- For the actual original Gauss parameter, dominance and parameter
preservation derive the common source/target tangent kernel. No kernel
comparison, quotient, proportionality scalar or target ruling is supplied. -/
theorem dominant_cone_original_parameter_common_tangent_kernels
    (H : Fin 4 → MvPolynomial (Fin 4) K) {d : ℕ} (hd : 0 < d) (hH : IsHomogMap H d)
    (hind : ¬ ComponentsDependent H) (hrank : polyRank (jac H) = 3) (I : ImageRelationWitness H)
    (e : RatFunc K ≃ₐ[K] projectiveRatioField (K := K)
      (rationalImageNormal H I.equation) (imageNormalPivot H I))
    (P : Fin 4 → MvPolynomial (Fin 4) K)
    (hdom : ∀ z : MvPolynomial (Fin 4) K,
      algebraMap (MvPolynomial (Fin 4) K) (imageRelationIdeal H).ResidueField (aeval P z) = 0 ↔
        z ∈ imageRelationIdeal H)
    (hpreserve : dominantConeRestriction (imageRelationIdeal H) P hdom
      (imageConeGaussHom H I e RatFunc.X) = imageConeGaussHom H I e RatFunc.X)
    (p q : MvPolynomial (Fin 4) K)
    (ht : imageConeGaussHom H I e RatFunc.X =
      algebraMap (MvPolynomial (Fin 4) K) (imageRelationIdeal H).ResidueField p /
        algebraMap (MvPolynomial (Fin 4) K) (imageRelationIdeal H).ResidueField q) :
    ∀ v : Fin 4 → (imageRelationIdeal H).ResidueField,
      mappedPolynomialGradient
        (algebraMap (MvPolynomial (Fin 4) K) (imageRelationIdeal H).ResidueField) I.equation ⬝ᵥ v = 0 →
      (polynomialRatioCovector
        (algebraMap (MvPolynomial (Fin 4) K) (imageRelationIdeal H).ResidueField) p q ⬝ᵥ v = 0 ↔
        polynomialRatioCovector
          ((algebraMap (MvPolynomial (Fin 4) K) (imageRelationIdeal H).ResidueField).comp
            (aeval P).toRingHom) p q ⬝ᵥ v = 0) := by
  let σ := dominantConeRestriction (imageRelationIdeal H) P hdom
  let ρ := algebraMap (MvPolynomial (Fin 4) K) (imageRelationIdeal H).ResidueField
  let φ := imageConeGaussHom H I e
  let r := mappedPolynomialGradient ρ I.equation
  let b := polynomialRatioCovector ρ p q
  let c := fun i => φ (rationalParameterDerivative K (gaussParameterNormal H I e i))
  obtain ⟨α, _hα, hnormal⟩ :=
    dominant_cone_original_gauss_parameter_constructs_common_normal H I e P hdom hpreserve
  have hr (i : Fin 4) : σ (r i) = α * r i := by
    change σ (ρ (pderiv i I.equation)) = _
    rw [dominantConeRestriction_polynomial]
    exact congrFun hnormal i
  have hfix : σ.comp φ = φ := rational_parameter_algHom_ext _ _ hpreserve
  have hc (i : Fin 4) : σ (c i) = c i :=
    DFunLike.congr_fun hfix (rationalParameterDerivative K (gaussParameterNormal H I e i))
  have hker := (original_cone_gauss_parameter_has_ruling_kernel H hd hH hind hrank I e p q ht).2
  have htransport := fixed_ruling_covector_transports_tangent_kernel σ.toRingHom r b c α hr hc hker
  have hb : (fun i => σ (b i)) = polynomialRatioCovector (ρ.comp (aeval P).toRingHom) p q := by
    funext i
    change σ ((ρ (pderiv i p) * ρ q - ρ p * ρ (pderiv i q)) / (ρ q) ^ 2) = _
    dsimp only [σ, ρ]
    simp only [map_div₀, map_sub, map_mul, map_pow, dominantConeRestriction_polynomial,
      polynomialRatioCovector, RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe]
  intro v hv
  rw [← hb]
  exact htransport v hv

end DimensionFourDependence
