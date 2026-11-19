import DimensionFourDependence.NormalizedPencilCategoricalMultiplicity
import DimensionFourDependence.ProjectiveHyperplaneAmpleness

/-! # Ampleness of the original pulled-back hyperplane bundle -/

namespace DimensionFourDependence

open AlgebraicGeometry CategoryTheory MvPolynomial TopologicalSpace

attribute [local instance] MvPolynomial.gradedAlgebra

universe u
set_option maxHeartbeats 4200000
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
local notation "U" a:max => Proj.basicOpen (homogeneousSubmodule (Fin 4) E) (X a)
local notation "hU" => extendedClosedGaussNormalizationProjectiveMap_chart_nonempty H I E hH e
local notation "w" => projectivePullbackHyperplaneWeight N f hU

local instance : IsIntegral N := extendedClosedGaussNormalizationScheme_isIntegral H I E hH e

/-- The actual pulled-back hyperplane bundle on the normalized pencil
is ample by the affine nonvanishing-cover criterion. The four original
coordinate sections already supply such a cover in degree one. -/
theorem extended_closed_gauss_pencil_pullback_hyperplane_affine_cover :
    ∃ s : Fin 4 → Γ(L, ⊤),
      IsCompact (Set.univ : Set N) ∧ (⨆ i : Fin 4, f ⁻¹ᵁ U i) = ⊤ ∧
      ∀ i : Fin 4, IsAffineOpen (f ⁻¹ᵁ U i) ∧ ∀ j : Fin 4,
        let t := (projectiveHyperplaneCategoricalPullbackIso N f hU).hom.app ⊤ (s i)
        (N).basicOpen (rationalFrameGlobalCoefficient N (fun a => f ⁻¹ᵁ U a) w
          ((f).iSup_preimage_eq_top (polynomialProjective_basicOpen_iSup E))
          (projectivePullbackHyperplaneWeight_ne_zero N f hU) t j) =
          (f ⁻¹ᵁ U j) ⊓ (f ⁻¹ᵁ U i) := by
  let : IsFinite f := extendedClosedGaussNormalizationProjectiveMap_isFinite H I E hH e
  let : IsNoetherian N := extendedClosedGaussNormalizationScheme_isNoetherian H I E hH e
  obtain ⟨_, hcompact, hcover, hnonvanishing⟩ :=
    projective_pullback_hyperplane_affine_nonvanishing_cover N f hU
  let g := (projectiveHyperplaneCategoricalPullbackIso N f hU).hom.app ⊤
  have hg : Function.Surjective g := (ConcreteCategory.bijective_of_isIso g).surjective
  choose s hs using fun i : Fin 4 => hg (projectivePullbackHyperplaneCoordinateSection N f hU i)
  refine ⟨s, hcompact, hcover, fun i => ⟨(hnonvanishing i).1, fun j => ?_⟩⟩
  change (N).basicOpen (rationalFrameGlobalCoefficient N _ w _ _ (g (s i)) j) = _
  rw [hs]
  exact (hnonvanishing i).2 j

end DimensionFourDependence
