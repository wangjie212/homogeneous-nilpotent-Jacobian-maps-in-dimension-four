import DimensionFourDependence.SourceRealizationFiberComponent
import DimensionFourDependence.RectangularJacobianRank
import DimensionFourDependence.GenericFiberOutput
import DimensionFourDependence.MatrixRankFieldMap

/-! # The entire original polynomial source evaluates faithfully on each actual component -/

namespace DimensionFourDependence

open MvPolynomial Matrix

universe u
set_option maxHeartbeats 2500000
set_option synthInstance.maxHeartbeats 100000

variable {K : Type u} [Field K]
local notation "R₀" => MvPolynomial (Fin 4) K
local notation "S₀" => FractionRing (MvPolynomial (Fin 4) K)

/-- A specified actual geometric component receives the original source
field by an original-constant algebra embedding retaining every original
polynomial value. All scalar compatibilities are constructed. -/
theorem geometric_component_constructs_original_source_algebra_embedding
    (H : Fin 4 → R₀) (E : Type u) [Field E] [Algebra (polynomialOutputField H) E]
    [Algebra K E] [IsScalarTower K (polynomialOutputField H) E]
    (P : Ideal (MvPolynomial (Fin 4) E)) [P.IsPrime]
    (hP : P ∈ (extendCoefficientIdeal E (fiberVanishingIdeal
      (L := polynomialOutputField H) (rationalCoordinate (K := K) (n := 4)))).minimalPrimes) :
    ∃ φ : S₀ →ₐ[K] FractionRing (MvPolynomial (Fin 4) E ⧸ P),
      ∀ p : R₀, φ (algebraMap R₀ S₀ p) = aeval (primeQuotientCoordinate P) p := by
  let M := polynomialOutputField H
  let G := FractionRing (MvPolynomial (Fin 4) E ⧸ P)
  obtain ⟨f, hf, hcompat⟩ := minimal_component_constructs_source_ringHom
    (rationalCoordinate (K := K) (n := 4)) (rationalSource_adjoin_coordinates_eq_top M) P hP
  have hK (c : K) : f (algebraMap K S₀ c) = algebraMap K G c := by
    change f (algebraMap M S₀ (algebraMap K M c)) = _
    rw [hcompat, ← IsScalarTower.algebraMap_apply K M E, ← IsScalarTower.algebraMap_apply K E G]
  let φ : S₀ →ₐ[K] G := { toRingHom := f, commutes' := hK }
  have he : φ.comp (IsScalarTower.toAlgHom K R₀ S₀) = aeval (primeQuotientCoordinate P) := by
    apply MvPolynomial.algHom_ext
    intro i
    simpa only [φ, AlgHom.comp_apply, IsScalarTower.coe_toAlgHom', aeval_X,
      AlgHom.coe_mk, rationalCoordinate] using hf i
  exact ⟨φ, fun p => DFunLike.congr_fun he p⟩

/-- The four original source coordinates remain algebraically
independent over the original constants on every actual component. -/
theorem geometric_component_original_source_coordinates_algebraicIndependent
    (H : Fin 4 → R₀) (E : Type u) [Field E] [Algebra (polynomialOutputField H) E]
    [Algebra K E] [IsScalarTower K (polynomialOutputField H) E]
    (P : Ideal (MvPolynomial (Fin 4) E)) [P.IsPrime]
    (hP : P ∈ (extendCoefficientIdeal E (fiberVanishingIdeal
      (L := polynomialOutputField H) (rationalCoordinate (K := K) (n := 4)))).minimalPrimes) :
    AlgebraicIndependent K (primeQuotientCoordinate P) := by
  obtain ⟨φ, hφ⟩ := geometric_component_constructs_original_source_algebra_embedding H E P hP
  have hc (i : Fin 4) : φ (rationalCoordinate (K := K) i) = primeQuotientCoordinate P i := by
    simpa only [aeval_X, rationalCoordinate] using hφ (X i)
  have he := (rationalCoordinates_algebraicIndependent (K := K) (n := 4)).map' (f := φ) φ.injective
  have hfun : φ ∘ rationalCoordinate (K := K) = primeQuotientCoordinate P := funext hc
  rw [hfun] at he
  exact he

/-- The actual Jacobian evaluated at the component generic point has
the same original rank; no generic rank assumption is supplied. -/
theorem geometric_component_original_evaluated_jacobian_rank
    (H : Fin 4 → R₀) (E : Type u) [Field E] [Algebra (polynomialOutputField H) E]
    [Algebra K E] [IsScalarTower K (polynomialOutputField H) E]
    (P : Ideal (MvPolynomial (Fin 4) E)) [P.IsPrime]
    (hP : P ∈ (extendCoefficientIdeal E (fiberVanishingIdeal
      (L := polynomialOutputField H) (rationalCoordinate (K := K) (n := 4)))).minimalPrimes) :
    ((jac H).map (aeval (primeQuotientCoordinate P) : R₀ →ₐ[K]
      FractionRing (MvPolynomial (Fin 4) E ⧸ P))).rank = polyRank (jac H) := by
  obtain ⟨φ, hφ⟩ := geometric_component_constructs_original_source_algebra_embedding H E P hP
  have hm : (jac H).map (aeval (primeQuotientCoordinate P) : R₀ →ₐ[K]
      FractionRing (MvPolynomial (Fin 4) E ⧸ P)) =
      ((jac H).map (algebraMap R₀ S₀)).map φ.toRingHom := by
    ext i j
    exact (hφ (jac H i j)).symm
  rw [hm, matrix_rank_field_map]
  rfl

end DimensionFourDependence
