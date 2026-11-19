import DimensionFourDependence.ClosedGaussPencilBaseChangeNormalization

/-! # Noetherianity of the intrinsic categorical normalization -/

namespace DimensionFourDependence

open AlgebraicGeometry CategoryTheory

universe u

set_option synthInstance.maxHeartbeats 100000
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {K : Type u} [Field K] [CharZero K]
  (H : Fin 4 → MvPolynomial (Fin 4) K) (I : ImageRelationWitness H)
  (E : Type u) [Field E] [Algebra (closedGaussParameterField H I) E]
  [Algebra.IsAlgebraic (closedGaussParameterField H I) E]
  {d : ℕ} (hH : IsHomogMap H d)
  (e : RatFunc K ≃ₐ[K] closedGaussParameterField H I)

/-- The normalization in the categorical pullback's own actual
function field is Noetherian, via the checked normalization isomorphism. -/
theorem closedGaussPencilCoefficientBaseChangeNormalization_isNoetherian :
    IsNoetherian (closedGaussPencilCoefficientBaseChangeNormalization H I E hH e) := by
  let : IsNoetherian (extendedClosedGaussNormalizationScheme H I E hH e) :=
    extendedClosedGaussNormalizationScheme_isNoetherian H I E hH e
  let n := extendedClosedGaussNormalizationCoefficientBaseChangeIso H I E hH e
  let : IsIso n.inv := n.isIso_inv
  let : IsLocallyNoetherian (closedGaussPencilCoefficientBaseChangeNormalization H I E hH e) :=
    isLocallyNoetherian_of_isOpenImmersion n.inv
  let : CompactSpace (closedGaussPencilCoefficientBaseChangeNormalization H I E hH e) :=
    QuasiCompact.compactSpace_of_compactSpace n.inv
  exact ⟨⟩

end DimensionFourDependence
