import DimensionFourDependence.NativePolynomialGermPointEquations

/-! # Native polynomial coefficient germs preserve the actual ring operations -/

namespace DimensionFourDependence

open MvPolynomial AlgebraicGeometry CategoryTheory

attribute [local instance] MvPolynomial.gradedAlgebra

universe u

set_option maxHeartbeats 2500000
set_option synthInstance.maxHeartbeats 100000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {K : Type u} [Field K] [CharZero K]
    (H : Fin 4 → MvPolynomial (Fin 4) K) (I : ImageRelationWitness H)
    (E : Type u) [Field E] [Algebra (closedGaussParameterField H I) E]
    [Algebra.IsAlgebraic (closedGaussParameterField H I) E]
    {d : ℕ} (hH : IsHomogMap H d)
    (e : RatFunc K ≃ₐ[K] closedGaussParameterField H I)

local notation "N" => extendedClosedGaussNormalizationScheme H I E hH e
local notation "V" a:max => extendedClosedGaussNormalizationChartOpen H I E hH e (finSuccEquiv' a)
local notation "f" => extendedClosedGaussNormalizationProjectiveMap H I E hH e
local notation "w" => extendedClosedGaussNormalizationHyperplaneWeight H I E hH e

local instance nativePolynomialGermHomIntegral : IsIntegral N :=
  extendedClosedGaussNormalizationScheme_isIntegral H I E hH e
noncomputable local instance nativePolynomialGermHomAlgebra : Algebra E (N).functionField :=
  extendedClosedGaussOwnFunctionFieldAlgebra H I E hH e

/-- The original regular polynomial coefficient at a specified
normalization point, with its actual source chart and germ maps. -/
noncomputable def nativePolynomialCoefficientGermHom
    (z : N) (a : Fin 4) (ha : z ∈ V a) :
    MvPolynomial (Fin 4) E →+* (N).presheaf.stalk z :=
  ((N).presheaf.germ (V a) z ha).hom.comp
    (((N).presheaf.map (homOfLE (le_of_eq
      (extendedClosedGaussNormalizationProjectiveMap_preimage H I E hH e a).symm)).op).hom.comp
      (projectivePullbackChartPolynomialHom (N) (f) a))

/-- The ring homomorphism is exactly the previously constructed
actual homogeneous source-form germ, for every polynomial. -/
theorem nativePolynomialCoefficientGermHom_apply
    (z : N) (a : Fin 4) (ha : z ∈ V a) (P : MvPolynomial (Fin 4) E) :
    nativePolynomialCoefficientGermHom H I E hH e z a ha P =
      extendedClosedGaussPolynomialCoefficientGerm H I E hH e P z a ha := rfl

/-- An exact native homogeneous power identity gives the same
identity among actual regular local coefficients, including its scalar. -/
theorem native_scaled_power_identity_germs
    (S L : MvPolynomial (Fin 4) E) (hS : S.IsHomogeneous d)
    (hL : L.IsHomogeneous 1) (c : E)
    (hpower : aeval (w) S = algebraMap E (N).functionField c * (aeval (w) L) ^ d)
    (z : N) (a : Fin 4) (ha : z ∈ V a) :
    extendedClosedGaussPolynomialCoefficientGerm H I E hH e S z a ha =
      nativePolynomialCoefficientGermHom H I E hH e z a ha (C c) *
        (extendedClosedGaussPolynomialCoefficientGerm H I E hH e L z a ha) ^ d := by
  let Q := S - C c * L ^ d
  have hQ : Q.IsHomogeneous d := hS.sub (by simpa only [one_mul] using (hL.pow d).C_mul c)
  have hzero : aeval (w) Q = 0 := by
    simp only [Q, map_sub, map_mul, aeval_C, map_pow, hpower, sub_self]
  have hg := (extendedClosedGaussPolynomialCoefficientGerm_eq_zero_iff
    H I E hH e Q hQ z a ha).mpr hzero
  change nativePolynomialCoefficientGermHom H I E hH e z a ha Q = 0 at hg
  simp only [Q, map_sub, map_mul, map_pow, sub_eq_zero] at hg
  exact hg

end DimensionFourDependence
