import DimensionFourDependence.ExtendedSourceFormLocalIdeals
import DimensionFourDependence.RulingRootProductIdentity

/-! # The zero locus of the actual root combination lies in both root and tangent plane -/

namespace DimensionFourDependence

open MvPolynomial AlgebraicGeometry

/-- The product-power identity forces both root and linear term to
vanish at every prime containing their nondegenerate combination. -/
theorem root_combination_prime_vanishing
    {R : Type*} [CommRing R] (P : Ideal R) [P.IsPrime]
    (U L r n α β : R) (d : ℕ) (hα : α ∉ P)
    (hcomb : U = α * L + β * r) (hprod : U * n = r ^ (d + 1)) (hU : U ∈ P) :
    r ∈ P ∧ L ∈ P := by
  have hr : r ∈ P := (inferInstance : P.IsPrime).mem_of_pow_mem (d + 1)
    (hprod ▸ P.mul_mem_right n hU)
  refine ⟨hr, (Ideal.IsPrime.mem_or_mem (inferInstance : P.IsPrime) ?_).resolve_left hα⟩
  have hdiff := P.sub_mem hU (P.mul_mem_left β hr)
  simpa only [hcomb, add_sub_cancel_right] using hdiff

universe u

set_option synthInstance.maxHeartbeats 100000
set_option maxHeartbeats 4000000
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

variable {K : Type u} [Field K] [CharZero K]
  (H : Fin 4 → MvPolynomial (Fin 4) K) (I : ImageRelationWitness H)
  (E : Type u) [Field E] [Algebra (closedGaussParameterField H I) E]
  [Algebra.IsAlgebraic (closedGaussParameterField H I) E]
  {d : ℕ} (hH : IsHomogMap H d)
  (e : RatFunc K ≃ₐ[K] closedGaussParameterField H I)

local notation "N" => extendedClosedGaussNormalizationScheme H I E hH e
local notation "M" => extendedClosedGaussNormalizationHyperplaneModuleSheaf H I E hH e
local notation "V" a:max => extendedClosedGaussNormalizationChartOpen H I E hH e (finSuccEquiv' a)
local notation "w" => extendedClosedGaussNormalizationHyperplaneWeight H I E hH e

local instance extendedRootCombinationVanishingIntegral : IsIntegral N :=
  extendedClosedGaussNormalizationScheme_isIntegral H I E hH e
local instance extendedRootCombinationVanishingNonempty (a : Fin 4) : Nonempty (V a) :=
  extendedClosedGaussNormalizationChartOpen_nonempty H I E hH e (finSuccEquiv' a)
noncomputable local instance extendedRootCombinationVanishingAlgebra : Algebra E (N).functionField :=
  extendedClosedGaussOwnFunctionFieldAlgebra H I E hH e

/-- On the actual normal scheme, vanishing of U forces the actual
regular root and the actual input linear section to vanish. This holds
at every point and needs neither divisor orders nor a multiplicity bound. -/
theorem actual_native_root_combination_vanishing
    (ν cS cN : Fin 4 → E) (r : (N).functionField) (hd : 0 < d)
    (hroot : r ^ d = aeval w (extendedClosedGaussOutputLinearPolynomial H I E cS))
    (α β : E) (hα : α ≠ 0)
    (hprod : extendedClosedGaussHyperplaneGlobalValue H I E hH e
        (extendedClosedGaussRootCombinationSection H I E hH e ν cS r hd hroot α β) *
          aeval w (extendedClosedGaussOutputLinearPolynomial H I E cN) = r ^ (d + 1))
    (z : N) (a : Fin 4) (ha : z ∈ V a)
    (hvan : (N).presheaf.germ (V a) z ha
      (extendedClosedGaussHyperplaneGlobalCoefficient H I E hH e
        (extendedClosedGaussRootCombinationSection H I E hH e ν cS r hd hroot α β) a) ∈
      IsLocalRing.maximalIdeal ((N).presheaf.stalk z)) :
    (N).presheaf.germ (V a) z ha
        (extendedClosedGaussHyperplaneGlobalCoefficient H I E hH e
          (extendedClosedGaussOutputLinearRootSection H I E hH e cS r hd hroot) a) ∈
        IsLocalRing.maximalIdeal ((N).presheaf.stalk z) ∧
      (N).presheaf.germ (V a) z ha
        (extendedClosedGaussHyperplaneGlobalCoefficient H I E hH e
          (extendedClosedGaussInputLinearSection H I E hH e ν) a) ∈
        IsLocalRing.maximalIdeal ((N).presheaf.stalk z) := by
  let g (s : Γ(M, ⊤)) := (N).presheaf.germ (V a) z ha
    (extendedClosedGaussHyperplaneGlobalCoefficient H I E hH e s a)
  let U := extendedClosedGaussRootCombinationSection H I E hH e ν cS r hd hroot α β
  let L := extendedClosedGaussInputLinearSection H I E hH e ν
  let R := extendedClosedGaussOutputLinearRootSection H I E hH e cS r hd hroot
  let n := (N).presheaf.germ (V a) z ha
    (extendedClosedGaussHyperplanePowerSectionCoefficient H I E hH e
      (extendedClosedGaussOutputLinearSection H I E hH e cN) a)
  let c (b : E) := (N).presheaf.germ ⊤ z (by trivial)
    (extendedClosedGaussGlobalConstantHom H I E hH e b)
  have hg (s : Γ(M, ⊤)) : algebraMap ((N).presheaf.stalk z) (N).functionField (g s) =
      extendedClosedGaussHyperplaneGlobalValue H I E hH e s / w a :=
    extendedClosedGaussHyperplaneGlobalCoefficient_germ_value H I E hH e s z a ha
  have hc (b : E) : algebraMap ((N).presheaf.stalk z) (N).functionField (c b) =
      algebraMap E (N).functionField b :=
    extendedClosedGaussGlobalConstantHom_germ_value H I E hH e b z
  have hn : algebraMap ((N).presheaf.stalk z) (N).functionField n =
      aeval w (extendedClosedGaussOutputLinearPolynomial H I E cN) / w a ^ d :=
    (Scheme.algebraMap_germ_eq_germToFunctionField N ha _).trans
      (extendedClosedGaussPowerSectionCoefficient_generic_value H I E hH e _ a)
  have hcomb : g U = c α * g L + c β * g R := by
    apply IsFractionRing.injective ((N).presheaf.stalk z) (N).functionField
    rw [map_add, map_mul, map_mul, hg, hg, hg, hc, hc]
    rw [extendedClosedGaussRootCombinationSection_value,
      extendedClosedGaussInputLinearSection_value, extendedClosedGaussOutputLinearRootSection_value]
    ring
  have hp : g U * n = g R ^ (d + 1) := by
    apply IsFractionRing.injective ((N).presheaf.stalk z) (N).functionField
    rw [map_mul, map_pow, hg, hg, hn, extendedClosedGaussOutputLinearRootSection_value,
      div_mul_div_comm, ← pow_succ', hprod, div_pow]
  exact root_combination_prime_vanishing (IsLocalRing.maximalIdeal ((N).presheaf.stalk z))
    (g U) (g L) (g R) n (c α) (c β) d
    (IsLocalRing.notMem_maximalIdeal.mpr
      ((extendedClosedGaussGlobalConstantHom_isUnit H I E hH e α hα).map
        ((N).presheaf.germ ⊤ z (by trivial)).hom)) hcomb hp hvan

end DimensionFourDependence
