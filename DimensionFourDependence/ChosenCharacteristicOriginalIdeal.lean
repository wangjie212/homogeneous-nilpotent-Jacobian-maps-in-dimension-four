import DimensionFourDependence.ExtendedChosenGaussCharacteristic
import DimensionFourDependence.ActualRootCharacteristicComparison
import DimensionFourDependence.GenericDirectionTangent

/-! # The chosen extended characteristic retains its entire original rational image ideal -/

namespace DimensionFourDependence

open MvPolynomial Matrix Module

attribute [local instance] MvPolynomial.gradedAlgebra

universe u

set_option quotPrecheck false
set_option maxHeartbeats 3000000
set_option synthInstance.maxHeartbeats 10000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {K : Type u} [Field K] [CharZero K]
  (H : Fin 4 → MvPolynomial (Fin 4) K) (I : ImageRelationWitness H)
  (E : Type u) [Field E] [Algebra (closedGaussParameterField H I) E]
  {d : ℕ} (hH : IsHomogMap H d) (hd : 0 < d)
  (hind : ¬ComponentsDependent H) (hGauss : gaussImageDimension H I = 1)

local notation "C₀" => closedGaussParameterField H I
local notation "e₀" => actualGaussRulingParameterChoice H I hH hd hind hGauss
local notation "v" => gaussParameterNormal H I (e₀)
local notation "ι" => extendedClosedGaussSourceCoefficientHom H I E

/-- Every nonzero vector of the same chosen extended characteristic
has exactly the original-field ideal of its original rational
characteristic. Both the coefficient embedding and line comparison
are constructed from the actual original map. -/
theorem chosen_extended_characteristic_original_point_ideal_eq
    (b : Fin 4 → RatFunc K) (hb : b ≠ 0)
    (hbC : b ∈ normalCharacteristicSubspace (rationalParameterDerivative K) (v))
    (W : Fin 4 → E) (hW0 : W ≠ 0)
    (hW : W ∈ extendedClosedGaussChosenCharacteristicSubspace H I E hH hd hind hGauss) :
    letI : Algebra K E := (ι).toAlgebra
    (projectiveFieldPointIdeal (E := K) W).toIdeal =
      (projectiveFieldPointIdeal (E := K) b).toIdeal := by
  letI : Algebra K E := (ι).toAlgebra
  letI : SMul K E := (ι).toAlgebra.toSMul
  letI : IsScalarTower K C₀ E := IsScalarTower.of_algebraMap_eq' rfl
  let f : RatFunc K →ₐ[K] E := (IsScalarTower.toAlgHom K C₀ E).comp
    (closedGaussOriginalParameterHom H I (e₀))
  let bE : Fin 4 → E := fun i => f (b i)
  have hbE : bE ≠ 0 := by
    intro he
    apply hb
    funext i
    apply f.injective
    simpa only [bE, Pi.zero_apply, map_zero, AlgHom.toRingHom_eq_coe,
      AlgHom.coe_toRingHom] using congrFun he i
  have hbEC : bE ∈ extendedClosedGaussChosenCharacteristicSubspace H I E hH hd hind hGauss := by
    change (normalCharacteristicMatrix (rationalParameterDerivative K) (v)).map f.toRingHom *ᵥ bE = 0
    change normalCharacteristicMatrix (rationalParameterDerivative K) (v) *ᵥ b = 0 at hbC
    funext i
    simpa only [Matrix.mulVec, dotProduct, Matrix.map_apply, bE, map_sum, map_mul,
      map_zero, Pi.zero_apply, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom]
        using congrArg f (congrFun hbC i)
  have hspan := extendedClosedGaussChosenCharacteristic_span_of_nonzero
    H I E hH hd hind hGauss bE hbE hbEC
  rw [← hspan] at hW
  obtain ⟨s, hs⟩ := Submodule.mem_span_singleton.mp hW
  have hs0 : s ≠ 0 := by
    intro he
    apply hW0
    rw [← hs, he, zero_smul]
  have he : W = fun i => s * f (b i) := hs.symm
  rw [he, projectiveFieldPointIdeal_scale _ s hs0]
  exact projectiveFieldPointIdeal_algHom b f

end DimensionFourDependence
