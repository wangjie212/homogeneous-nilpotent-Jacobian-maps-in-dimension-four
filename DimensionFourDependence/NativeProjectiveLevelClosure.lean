import DimensionFourDependence.NativePolynomialGermHom
import DimensionFourDependence.AffineStalkLevelClosure

/-! # Native local quotient levels give original homogeneous projective levels -/

namespace DimensionFourDependence

open MvPolynomial AlgebraicGeometry CategoryTheory

attribute [local instance] MvPolynomial.gradedAlgebra

universe u

set_option quotPrecheck false
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
local notation "germ" P:max z:max a:max hz:max =>
  extendedClosedGaussPolynomialCoefficientGerm H I E hH e P z a hz

local instance nativeProjectiveLevelClosureIntegral : IsIntegral N :=
  extendedClosedGaussNormalizationScheme_isIntegral H I E hH e
noncomputable local instance nativeProjectiveLevelClosureAlgebra : Algebra E (N).functionField :=
  extendedClosedGaussOwnFunctionFieldAlgebra H I E hH e

/-- Polynomial constants in the native chart have exactly the germ
of the original global coefficient constant, including at the vertex. -/
theorem native_constant_polynomial_germ_eq_global_constant_germ
    (c : E) (z : N) (a : Fin 4) (hz : z ∈ V a) :
    germ (C c) z a hz = (N).presheaf.germ ⊤ z (by trivial)
      (extendedClosedGaussGlobalConstantHom H I E hH e c) := by
  apply IsFractionRing.injective ((N).presheaf.stalk z) (N).functionField
  rw [extendedClosedGaussPolynomialCoefficientGerm_value H I E hH e (C c)
      (isHomogeneous_C _ c) z a hz,
    extendedClosedGaussGlobalConstantHom_germ_value, aeval_C, pow_zero, div_one]

/-- Accumulation of an actual local quotient level implies accumulation
of the same homogeneous level on the actual normalization, on the
original normal-denominator open. No abstract field identification is used. -/
theorem native_local_level_closure_implies_projective_level_closure
    (P L : MvPolynomial (Fin 4) E) (hd : 0 < d) (hP : P.IsHomogeneous d) (hL : L.IsHomogeneous 1)
    (c : E) (z : N) (a : Fin 4) (hz : z ∈ V a)
    (hlevel : IsLocalRing.closedPoint ((N).presheaf.stalk z) ∈
      closure (quotientLevelLocus ((N).presheaf.stalk z)
        (germ P z a hz) ((germ L z a hz) ^ d)
        ((N).presheaf.germ ⊤ z (by trivial) (extendedClosedGaussGlobalConstantHom H I E hH e c)))) :
    z ∈ closure {y : N | L ∉ ((f) y).asHomogeneousIdeal ∧
      P - C c * L ^ d ∈ ((f) y).asHomogeneousIdeal} := by
  let A := Γ(N, V a)
  let n : A := extendedClosedGaussChartPolynomialCoefficient H I E hH e P a
  let l : A := extendedClosedGaussChartPolynomialCoefficient H I E hH e L a
  let k : A := extendedClosedGaussChartPolynomialCoefficient H I E hH e (C c) a
  let hV := extendedClosedGaussNormalizationChartOpen_isAffineOpen H I E hH e (finSuccEquiv' a)
  have hlocal : IsLocalRing.closedPoint ((N).presheaf.stalk z) ∈
      closure (quotientLevelLocus ((N).presheaf.stalk z)
        ((N).presheaf.germ (V a) z hz n) ((N).presheaf.germ (V a) z hz (l ^ d))
        ((N).presheaf.germ (V a) z hz k)) := by
    rw [map_pow]
    change IsLocalRing.closedPoint ((N).presheaf.stalk z) ∈
      closure (quotientLevelLocus ((N).presheaf.stalk z)
        (extendedClosedGaussPolynomialCoefficientGerm H I E hH e P z a hz)
        ((extendedClosedGaussPolynomialCoefficientGerm H I E hH e L z a hz) ^ d)
        (extendedClosedGaussPolynomialCoefficientGerm H I E hH e (C c) z a hz))
    rw [native_constant_polynomial_germ_eq_global_constant_germ]
    exact hlevel
  have hchart := affine_stalk_level_closure_maps_to_chart_level_closure
    (V a) hV z hz n (l ^ d) k hlocal
  apply closure_mono _ hchart
  rintro y ⟨p, hp, rfl⟩
  have hy : hV.fromSpec p ∈ V a := by
    change hV.fromSpec p ∈ (V a : Set N)
    rw [← hV.range_fromSpec]
    exact Set.mem_range_self p
  letI : Algebra A ((N).presheaf.stalk (hV.fromSpec p)) :=
    (N).presheaf.algebra_section_stalk ⟨hV.fromSpec p, hy⟩
  letI : IsLocalization.AtPrime ((N).presheaf.stalk (hV.fromSpec p)) p.asIdeal :=
    hV.isLocalization_stalk' p hy
  have hmem (r : A) : r ∈ p.asIdeal ↔
      (N).presheaf.germ (V a) (hV.fromSpec p) hy r ∈
        IsLocalRing.maximalIdeal ((N).presheaf.stalk (hV.fromSpec p)) := by
    exact (IsLocalization.AtPrime.to_map_mem_maximal_iff _ p.asIdeal r).symm
  refine ⟨?_, ?_⟩
  · intro hLy
    have hl : l ∈ p.asIdeal := (hmem l).mpr
      ((native_polynomial_germ_mem_maximal_iff_projective_equation H I E hH e L hL _ a hy).mpr hLy)
    exact hp.1 ((p.isPrime.pow_mem_iff_mem d hd).mpr hl)
  · apply (native_polynomial_germ_mem_maximal_iff_projective_equation H I E hH e
      (P - C c * L ^ d) (hP.sub (by simpa only [one_mul] using (hL.pow d).C_mul c)) _ a hy).mp
    have he := (hmem (n - k * l ^ d)).mp hp.2
    change nativePolynomialCoefficientGermHom H I E hH e (hV.fromSpec p) a hy
      (P - C c * L ^ d) ∈ _
    have he' : extendedClosedGaussPolynomialCoefficientGerm H I E hH e P (hV.fromSpec p) a hy -
        extendedClosedGaussPolynomialCoefficientGerm H I E hH e (C c) (hV.fromSpec p) a hy *
          (extendedClosedGaussPolynomialCoefficientGerm H I E hH e L (hV.fromSpec p) a hy) ^ d ∈
        IsLocalRing.maximalIdeal ((N).presheaf.stalk (hV.fromSpec p)) := by
      simpa only [map_sub, map_mul, map_pow, n, k, l,
        extendedClosedGaussPolynomialCoefficientGerm] using he
    simpa only [map_sub, map_mul, map_pow, nativePolynomialCoefficientGermHom_apply] using he'

end DimensionFourDependence
