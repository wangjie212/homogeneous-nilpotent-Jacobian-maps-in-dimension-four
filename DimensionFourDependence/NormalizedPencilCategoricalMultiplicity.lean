import DimensionFourDependence.CategoricalProjectiveHyperplanePullback
import DimensionFourDependence.ExtendedNativeSectionMultiplicity

/-! # The multiplicity bound for sections of the actual categorical pullback -/

namespace DimensionFourDependence

open AlgebraicGeometry CategoryTheory MvPolynomial TopologicalSpace

universe u
set_option maxHeartbeats 3900000
set_option synthInstance.maxHeartbeats 140000
set_option quotPrecheck false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {K : Type u} [Field K] [CharZero K]
  (H : Fin 4 → MvPolynomial (Fin 4) K) (I : ImageRelationWitness H)
  (E : Type u) [Field E] [Algebra (closedGaussParameterField H I) E]
  [Algebra.IsAlgebraic (closedGaussParameterField H I) E]
  {d : ℕ} (hH : IsHomogMap H d)
  (e : RatFunc K ≃ₐ[K] closedGaussParameterField H I)

local notation "N" => extendedClosedGaussNormalizationScheme H I E hH e
local notation "f" => extendedClosedGaussNormalizationProjectiveMap H I E hH e
local notation "L" => (Scheme.Modules.pullback f).obj (projectiveHyperplaneModuleSheaf E)
local notation "U" a:max => extendedClosedGaussNormalizationChartOpen H I E hH e (finSuccEquiv' a)
local instance : IsIntegral N := extendedClosedGaussNormalizationScheme_isIntegral H I E hH e
local instance : IsNoetherian N := extendedClosedGaussNormalizationScheme_isNoetherian H I E hH e

/-- The original projective map of the normalized pencil is finite. -/
theorem extendedClosedGaussNormalizationProjectiveMap_isFinite : IsFinite f := by
  let : IsFinite (extendedClosedGaussNormalizationSchemeMap H I E hH e) :=
    extendedClosedGaussNormalizationSchemeMap_isFinite H I E hH e
  let : IsClosedImmersion (extendedClosedGaussPencilSchemeInclusion H I E hH e) :=
    extendedClosedGaussPencilSchemeInclusion_isClosedImmersion H I E hH e
  unfold extendedClosedGaussNormalizationProjectiveMap
  infer_instance

/-- Every nonzero global section of the pullback of the original
hyperplane bundle has multiplicity between zero and the pencil degree
at every intrinsic prime divisor of the normalized pencil. -/
theorem actual_categorical_pencil_global_section_multiplicity_bound
    (hGauss : gaussImageDimension H I = 1)
    (p q : MvPolynomial (Fin 4) K) {D : ℕ}
    (hq : q ≠ 0) (hrel : IsRelPrime p q) (hpH : p.IsHomogeneous D) (hqH : q.IsHomogeneous D)
    (ht : closedGaussParameterSourceHom H I e RatFunc.X =
      algebraMap _ (FractionRing (MvPolynomial (Fin 4) K)) p /
        algebraMap _ (FractionRing (MvPolynomial (Fin 4) K)) q)
    (s : Γ(L, ⊤)) (hs : s ≠ 0) (z : N) (hcodim : Order.coheight z = 1) :
    ∃ (a : Fin 4) (hz : z ∈ U a),
      let t := (extendedClosedGaussHyperplaneCategoricalPullbackIso H I E hH e).hom.app ⊤ s
      let r := (N).presheaf.germ (U a) z hz
        (extendedClosedGaussHyperplaneGlobalCoefficient H I E hH e t a)
      0 ≤ (N).ord (algebraMap ((N).presheaf.stalk z) (N).functionField r) z ∧
        (N).ord (algebraMap ((N).presheaf.stalk z) (N).functionField r) z ≤ (D : ℤ) := by
  let g := (extendedClosedGaussHyperplaneCategoricalPullbackIso H I E hH e).hom.app ⊤
  have hg : Function.Injective g := (ConcreteCategory.bijective_of_isIso g).injective
  have ht₀ : g s ≠ 0 := by
    intro h
    have hzero : g (0 : Γ(L, ⊤)) = 0 := g.hom.map_zero
    exact hs (hg (h.trans hzero.symm))
  exact actual_native_pencil_global_section_all_divisors_multiplicity_bound H I E hH e hGauss
    p q hq hrel hpH hqH ht (g s) ht₀ z hcodim

end DimensionFourDependence
