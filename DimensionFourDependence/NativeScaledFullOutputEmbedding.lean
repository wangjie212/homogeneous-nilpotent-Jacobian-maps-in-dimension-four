import DimensionFourDependence.NativeScaleAlgebraicCoefficients
import DimensionFourDependence.CompatibleFullOutputEmbedding
import DimensionFourDependence.ScaledRulingParameterAlgebraicity

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

local instance nativeScaledFullOutputEmbeddingIntegral : IsIntegral N :=
  extendedClosedGaussNormalizationScheme_isIntegral H I E hH e
noncomputable local instance nativeScaledFullOutputEmbeddingExtendedAlgebra : Algebra E (N).functionField :=
  extendedClosedGaussOwnFunctionFieldAlgebra H I E hH e
noncomputable local instance nativeScaledFullOutputEmbeddingOriginalAlgebra : Algebra K (N).functionField :=
  extendedClosedGaussOriginalSourceAlgebra H I E hH e

include hd

/-- Exact original generic target equations construct the embedding of
the entire original K(H) in E(lambda)(r). The embedding preserves every
original output and ground coefficient, commutes with the actual source
embedding on every output-field element, and makes the entire rational
coefficient field algebraic over K(H). No parameter is specialized. -/
theorem native_scaled_generic_target_constructs_algebraic_full_output_embedding
    (L : MvPolynomial (Fin 4) E) (hL : aeval (R := E) (w) L ≠ 0)
    (s n bS bN : Fin 4 → E)
    (hsS : s ⬝ᵥ bS = 1) (hnS : n ⬝ᵥ bS = 0)
    (hsN : s ⬝ᵥ bN = 0) (hnN : n ⬝ᵥ bN = 1)
    (a : E) (ha : a ≠ 0) (α : RatFunc E →ₐ[E] (N).functionField) :
    letI : Algebra (RatFunc E) (N).functionField := α.toRingHom.toAlgebra
    ∀ (γ : Cᵣ →ₐ[RatFunc E] Gᵣ), γ RatFunc.X = RatFunc.X →
      (∀ i, aeval (R := E)
        (fun j => RatFunc.X * RatFunc.C ((w) j / aeval (R := E) (w) L)) (MvPolynomial.map (ι) (H i)) =
          γ (RatFunc.X ^ d * RatFunc.C
            (RatFunc.C (a ^ d * bS i) + RatFunc.X * RatFunc.C (bN i)))) →
      ∃ δ : D₀ →+* Cᵣ,
        (∀ c : K, δ (algebraMap K D₀ c) = RatFunc.C (RatFunc.C ((ι) c))) ∧
        (∀ i, δ (fullOutputCoordinate (K := K) (H₀) i) =
          RatFunc.X ^ d * RatFunc.C (RatFunc.C (a ^ d * bS i) + RatFunc.X * RatFunc.C (bN i))) ∧
        (∀ q : D₀, γ (δ q) = nativeIndependentScaleSourceFieldHom H I E hH e L hL (q : S₀)) ∧
        letI : Algebra D₀ Cᵣ := δ.toAlgebra
        Algebra.IsAlgebraic D₀ Cᵣ := by
  letI : Algebra (RatFunc E) (N).functionField := α.toRingHom.toAlgebra
  intro γ hγ htarget
  let Φ := nativeIndependentScaleSourceFieldHom H I E hH e L hL
  let Y : Fin 4 → Cᵣ := fun i => RatFunc.X ^ d * RatFunc.C
    (RatFunc.C (a ^ d * bS i) + RatFunc.X * RatFunc.C (bN i))
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
  have hY (i : Fin 4) : Φ ((H₀) i) = Γ (Y i) :=
    (nativeIndependentScaleSourceFieldHom_extended_polynomial H I E hH e L hL (H i)).trans (htarget i)
  let δ₀ : D₀ →ₐ[K] Cᵣ := compatibleFullOutputFieldHom Φ Γ (H₀) Y hY
  have hcompat (q : D₀) : γ (δ₀ q) = Φ (q : S₀) :=
    compatibleFullOutputFieldHom_source_value Φ Γ (H₀) Y hY q
  refine ⟨δ₀.toRingHom, ?_, ?_, hcompat, ?_⟩
  · intro c
    exact δ₀.commutes c
  · intro i
    exact compatibleFullOutputFieldHom_coordinate Φ Γ (H₀) Y hY i
  · letI : Algebra D₀ Cᵣ := δ₀.toRingHom.toAlgebra
    letI : Algebra D₀ Gᵣ := nativeIndependentScaleFullOutputAlgebra H I E hH e L hL
    let ΓD : Cᵣ →ₐ[D₀] Gᵣ := { γ.toRingHom with commutes' := hcompat }
    let τ : E →+* Gᵣ := RatFunc.C.comp (algebraMap E (N).functionField)
    have hcoeff (b : E) : IsAlgebraic D₀ (τ b) :=
      native_independent_scale_extended_coefficient_algebraic_over_full_output H I E hH e L hL b
    let Ys : Fin 4 → Gᵣ := fun i => Φ ((H₀) i)
    have houtput (i : Fin 4) : IsAlgebraic D₀ (Ys i) := by
      change IsAlgebraic D₀ (algebraMap D₀ Gᵣ (fullOutputCoordinate (K := K) (H₀) i))
      exact isAlgebraic_algebraMap _
    have hscaled (i : Fin 4) : Ys i = RatFunc.X ^ d *
        (τ (a ^ d * bS i) + RatFunc.C (α RatFunc.X) * τ (bN i)) := by
      change Φ ((H₀) i) = _
      rw [hY i]
      change γ (Y i) = _
      simp only [Y, map_mul, map_pow, map_add, hγ, hγC, hαC, τ, RingHom.comp_apply]
    obtain ⟨hralg, hlevelalg⟩ := scaled_ruling_parameters_algebraic_of_original_output_values
      τ hcoeff s n bS bN hsS hnS hsN hnN a ha d hd
      RatFunc.X (RatFunc.C (α RatFunc.X)) RatFunc.X_ne_zero Ys hscaled houtput
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
