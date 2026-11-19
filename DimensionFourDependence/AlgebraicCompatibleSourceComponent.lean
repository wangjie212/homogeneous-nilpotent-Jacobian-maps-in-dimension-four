import DimensionFourDependence.CompatibleFullOutputEmbedding
import DimensionFourDependence.FiberAlgebraicBaseChange
import DimensionFourDependence.ProjectiveLineAtlasPoints

/-! # Compatible algebraic coefficient extensions identify actual full-fiber components -/

namespace DimensionFourDependence

open MvPolynomial

attribute [local instance] MvPolynomial.algebraMvPolynomial

set_option maxHeartbeats 3000000
set_option synthInstance.maxHeartbeats 100000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- An actual source-field embedding over the original coefficient
field identifies the relation prime of its actual coordinates with a
minimal component after the given algebraic coefficient extension. -/
theorem compatible_algebraic_source_relations_form_actual_component
    {L C S G : Type*} [Field L] [Field C] [Field S] [Field G]
    [Algebra L C] [Algebra L S] [Algebra C G] [Algebra L G]
    [IsScalarTower L C G] [Algebra.IsAlgebraic L C] {n : ℕ}
    (Φ : S →ₐ[L] G) (x : Fin n → S) (v : Fin n → G)
    (hcoords : ∀ i, Φ (x i) = v i) :
    fiberVanishingIdeal (L := C) v ∈
      (extendCoefficientIdeal C (fiberVanishingIdeal (L := L) x)).minimalPrimes := by
  let P := fiberVanishingIdeal (L := C) v
  have hcontract : P.comap (MvPolynomial.map (algebraMap L C)) = fiberVanishingIdeal (L := L) x := by
    ext Q
    change aeval (R := C) v (MvPolynomial.map (algebraMap L C) Q) = 0 ↔ aeval x Q = 0
    rw [aeval_map_algebra_extension]
    have he := comp_aeval_apply x Φ Q
    rw [show (fun i => Φ (x i)) = v from funext hcoords] at he
    rw [← he]
    exact map_eq_zero_iff _ Φ.injective
  have hint : (MvPolynomial.map (algebraMap L C) (σ := Fin n)).IsIntegral := by
    rw [← MvPolynomial.algebraMap_def]
    exact algebraMap_isIntegral_iff.mpr inferInstance
  exact prime_minimal_over_integral_extension (MvPolynomial.map (algebraMap L C)) hint
    (fiberVanishingIdeal (L := L) x) P hcontract

/-- A coefficient embedding of the entire original K(H), compatible
with the actual original rational source embedding, identifies an actual
component of the original full generic fiber in the same source labels. -/
theorem original_full_output_compatible_source_constructs_actual_component
    {K C G : Type*} [Field K] [Field C] [Field G]
    (H : Fin 4 → MvPolynomial (Fin 4) K)
    (δ : polynomialOutputField H →+* C) (γ : C →+* G)
    (Φ : FractionRing (MvPolynomial (Fin 4) K) →+* G)
    (hcompat : ∀ q : polynomialOutputField H, γ (δ q) = Φ (q : FractionRing (MvPolynomial (Fin 4) K)))
    (v : Fin 4 → G) (hcoords : ∀ i, Φ (rationalCoordinate (K := K) i) = v i) :
    letI : Algebra (polynomialOutputField H) C := δ.toAlgebra
    letI : Algebra C G := γ.toAlgebra
    Algebra.IsAlgebraic (polynomialOutputField H) C →
      fiberVanishingIdeal (L := C) v ∈
        (extendCoefficientIdeal C (fiberVanishingIdeal (L := polynomialOutputField H)
          (rationalCoordinate (K := K) (n := 4)))).minimalPrimes := by
  letI : Algebra (polynomialOutputField H) C := δ.toAlgebra
  letI : Algebra C G := γ.toAlgebra
  intro halg
  letI : Algebra.IsAlgebraic (polynomialOutputField H) C := halg
  letI : Algebra (polynomialOutputField H) G := (γ.comp δ).toAlgebra
  letI : IsScalarTower (polynomialOutputField H) C G := IsScalarTower.of_algebraMap_eq' rfl
  let ΦD : FractionRing (MvPolynomial (Fin 4) K) →ₐ[polynomialOutputField H] G :=
    { Φ with commutes' := fun q => (hcompat q).symm }
  exact compatible_algebraic_source_relations_form_actual_component ΦD
    (rationalCoordinate (K := K) (n := 4)) v hcoords

end DimensionFourDependence
