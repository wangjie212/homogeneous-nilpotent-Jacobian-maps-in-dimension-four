import DimensionFourDependence.NativeScaleAlgebraicCoefficients
import DimensionFourDependence.CompatibleFullOutputEmbedding
import DimensionFourDependence.CharacteristicScaleParameterAlgebraicity
import DimensionFourDependence.CharacteristicScaleCoefficientImages

/-! # The two-parameter native target is an actual algebraic extension of K(H) -/

namespace DimensionFourDependence

open MvPolynomial Matrix AlgebraicGeometry

universe u

set_option quotPrecheck false
set_option maxHeartbeats 5000000
set_option synthInstance.maxHeartbeats 100000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {K : Type u} [Field K] [CharZero K]
    (H : Fin 4 → MvPolynomial (Fin 4) K) (I : ImageRelationWitness H)
    (E : Type u) [Field E] [Algebra (closedGaussParameterField H I) E]
    [Algebra.IsAlgebraic (closedGaussParameterField H I) E]
    {d : ℕ} (hd : 0 < d) (hH : IsHomogMap H d)
    (e : RatFunc K ≃ₐ[K] closedGaussParameterField H I)

local notation "N" => extendedClosedGaussNormalizationScheme H I E hH e
local notation "w" => extendedClosedGaussNormalizationHyperplaneWeight H I E hH e
local notation "ι" => extendedClosedGaussSourceCoefficientHom H I E
local notation "S₀" => FractionRing (MvPolynomial (Fin 4) K)
local notation "D₀" => polynomialOutputField H
local notation "Cᵣ" => RatFunc (RatFunc E)
local notation "Gᵣ" => RatFunc (N).functionField
local notation "H₀" => (fun i => algebraMap (MvPolynomial (Fin 4) K) S₀ (H i))

local instance nativeCharacteristicFullOutputEmbeddingIntegral : IsIntegral N :=
  extendedClosedGaussNormalizationScheme_isIntegral H I E hH e
noncomputable local instance nativeCharacteristicFullOutputEmbeddingExtendedAlgebra : Algebra E (N).functionField :=
  extendedClosedGaussOwnFunctionFieldAlgebra H I E hH e
noncomputable local instance nativeCharacteristicFullOutputEmbeddingOriginalAlgebra : Algebra K (N).functionField :=
  extendedClosedGaussOriginalSourceAlgebra H I E hH e

variable (hind : ¬ComponentsDependent H) (hGauss : gaussImageDimension H I = 1)

local notation "ν₀" => extendedClosedGaussChosenRulingMatrix H I E hH hd hind hGauss 0
local notation "L₀" => linearFormPolynomial (ν₀)
local notation "T₀" => ∑ j, algebraMap E (N).functionField ((ν₀) j) * (w) j
local notation "Y₀" => fun i => aeval (w) (MvPolynomial.map (ι) (H i))

/-- The characteristic factorization constructs the compatible full
original output embedding over E(lambda)(s). Its constants, original
outputs and source realization are retained, and the whole two-parameter
field is proved algebraic over the original full output field. -/
theorem native_characteristic_scaled_factorization_constructs_algebraic_full_output_embedding
    (r : (N).functionField) (V W : Fin 4 → E) (hVW : LinearIndependent E ![V, W])
    (hfactor : ∀ i, (Y₀) i = r ^ (d - 1) *
      (r * algebraMap E (N).functionField (V i) + (T₀) * algebraMap E (N).functionField (W i)))
    (hT : (T₀) ≠ 0) (α : RatFunc E →ₐ[E] (N).functionField)
    (hα : α RatFunc.X = r / (T₀)) :
    letI : Algebra (RatFunc E) (N).functionField := α.toRingHom.toAlgebra
    ∀ (γ : Cᵣ →ₐ[RatFunc E] Gᵣ), γ RatFunc.X = RatFunc.X →
      ∃ δ : D₀ →+* Cᵣ,
        (∀ c : K, δ (algebraMap K D₀ c) = RatFunc.C (RatFunc.C ((ι) c))) ∧
        (∀ i, δ (fullOutputCoordinate (K := K) (H₀) i) = RatFunc.X ^ d *
          RatFunc.C (RatFunc.X ^ (d - 1) * (RatFunc.X * RatFunc.C (V i) + RatFunc.C (W i)))) ∧
        (∀ q : D₀, γ (δ q) =
          nativeCharacteristicScaleSourceHom H I E hH e hd hind hGauss hT (q : S₀)) ∧
        letI : Algebra D₀ Cᵣ := δ.toAlgebra
        Algebra.IsAlgebraic D₀ Cᵣ := by
  letI : Algebra (RatFunc E) (N).functionField := α.toRingHom.toAlgebra
  intro γ hγ
  have hL : aeval (R := E) (w) (L₀) ≠ 0 := by
    simpa only [linearFormPolynomial, map_sum, map_mul, aeval_C, aeval_X] using hT
  let Φ := nativeIndependentScaleSourceFieldHom H I E hH e (L₀) hL
  let Y : Fin 4 → Cᵣ := fun i => RatFunc.X ^ d *
    RatFunc.C (RatFunc.X ^ (d - 1) * (RatFunc.X * RatFunc.C (V i) + RatFunc.C (W i)))
  have hγC (b : RatFunc E) : γ (RatFunc.C b) = RatFunc.C (α b) := by
    exact (γ.commutes b).trans (IsScalarTower.algebraMap_apply (RatFunc E) (N).functionField Gᵣ b)
  have hαC (b : E) : α (RatFunc.C b) = algebraMap E (N).functionField b := α.commutes b
  letI : Algebra K Cᵣ := ((RatFunc.C.comp RatFunc.C).comp (ι)).toAlgebra
  let Γ : Cᵣ →ₐ[K] Gᵣ :=
    { γ.toRingHom with
      commutes' := fun c => by
        change γ (RatFunc.C (RatFunc.C ((ι) c))) =
          RatFunc.C (algebraMap E (N).functionField ((ι) c))
        rw [hγC, hαC] }
  have hsource (i : Fin 4) : Φ ((H₀) i) =
      RatFunc.X ^ d * RatFunc.C ((Y₀) i / (T₀) ^ d) := by
    simpa only [Φ, linearFormPolynomial, map_sum, map_mul, aeval_C, aeval_X] using
      nativeIndependentScaleSourceFieldHom_homogeneous_polynomial H I E hH e (L₀) hL (H i) (hH i)
  have hY (i : Fin 4) : Φ ((H₀) i) = Γ (Y i) := by
    rw [hsource i, hfactor i, root_factorization_normalized_value r (T₀) _ _ hT hd]
    change _ = γ (Y i)
    simp only [Y, map_mul, map_pow, map_add, hγ, hγC, hαC, hα]
  let δ₀ : D₀ →ₐ[K] Cᵣ := compatibleFullOutputFieldHom Φ Γ (H₀) Y hY
  have hcompat (q : D₀) : γ (δ₀ q) = Φ (q : S₀) :=
    compatibleFullOutputFieldHom_source_value Φ Γ (H₀) Y hY q
  refine ⟨δ₀.toRingHom, ?_, ?_, hcompat, ?_⟩
  · intro c
    exact δ₀.commutes c
  · intro i
    exact compatibleFullOutputFieldHom_coordinate Φ Γ (H₀) Y hY i
  · letI : Algebra D₀ Cᵣ := δ₀.toRingHom.toAlgebra
    letI : Algebra D₀ Gᵣ := nativeIndependentScaleFullOutputAlgebra H I E hH e (L₀) hL
    let ΓD : Cᵣ →ₐ[D₀] Gᵣ := { γ.toRingHom with commutes' := hcompat }
    let τ : E →+* Gᵣ := RatFunc.C.comp (algebraMap E (N).functionField)
    have hcoeff (b : E) : IsAlgebraic D₀ (τ b) :=
      native_independent_scale_extended_coefficient_algebraic_over_full_output H I E hH e (L₀) hL b
    let Ys : Fin 4 → Gᵣ := fun i => Φ ((H₀) i)
    have houtput (i : Fin 4) : IsAlgebraic D₀ (Ys i) := by
      change IsAlgebraic D₀ (algebraMap D₀ Gᵣ (fullOutputCoordinate (K := K) (H₀) i))
      exact isAlgebraic_algebraMap _
    have hscaled (i : Fin 4) : Ys i = RatFunc.X ^ d * (RatFunc.C (α RatFunc.X)) ^ (d - 1) *
        (RatFunc.C (α RatFunc.X) * τ (V i) + τ (W i)) := by
      change Φ ((H₀) i) = _
      rw [hY i]
      change γ (Y i) = _
      simp only [Y, map_mul, map_pow, map_add, hγ, hγC, hαC, τ, RingHom.comp_apply]
      ring
    have ht0 : RatFunc.C (α RatFunc.X) ≠ 0 :=
      (map_ne_zero RatFunc.C).mpr ((map_ne_zero α).mpr RatFunc.X_ne_zero)
    obtain ⟨hralg, hlevelalg⟩ := characteristic_scale_parameters_algebraic_of_original_output_values
      τ hcoeff V W hVW d hd RatFunc.X (RatFunc.C (α RatFunc.X)) RatFunc.X_ne_zero ht0 Ys hscaled houtput
    have himages (z : Cᵣ) : IsAlgebraic D₀ (γ z) := by
      apply two_parameter_rational_function_images_algebraic γ.toRingHom _ _ _ z
      · intro b
        change IsAlgebraic D₀ (γ (RatFunc.C (RatFunc.C b)))
        rw [hγC, hαC]
        exact hcoeff b
      · change IsAlgebraic D₀ (γ (RatFunc.C RatFunc.X))
        rw [hγC]
        exact hlevelalg
      · change IsAlgebraic D₀ (γ RatFunc.X)
        rw [hγ]
        exact hralg
    constructor
    intro z
    exact (isAlgebraic_algHom_iff ΓD ΓD.injective).mp (himages z)

end DimensionFourDependence
