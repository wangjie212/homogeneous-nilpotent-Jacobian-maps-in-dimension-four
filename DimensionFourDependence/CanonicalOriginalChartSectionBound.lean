import DimensionFourDependence.OriginalChartResidueProjectionBound
import DimensionFourDependence.NormalizationPrimeFunctionField

/-! # The original-chart section bound in the actual height-one normalization stalk

Normality, the common fraction field, the nonfield local center and the
local projection actions are constructed from the original affine ring
and its actual normalization prime.
-/

namespace DimensionFourDependence

universe u

open MvPolynomial

set_option synthInstance.maxHeartbeats 100000
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

variable {A : Type u} [CommRing A] [IsDomain A]

/-- Every actual prime-local ring of the canonical normalization is normal. -/
theorem normalization_prime_local_isIntegrallyClosed
    (Q : Ideal (normalizationRing A)) [Q.IsPrime] :
    IsIntegrallyClosed (Localization.AtPrime Q) := by
  let : IsIntegrallyClosed (normalizationRing A) := normalizationRing_isIntegrallyClosed A
  exact isIntegrallyClosed_of_isLocalization (Localization.AtPrime Q)
    Q.primeCompl Q.primeCompl_le_nonZeroDivisors

/-- An actual height-one normalization prime gives a nonfield local ring. -/
theorem normalization_prime_local_maximalIdeal_ne_bot
    (Q : Ideal (normalizationRing A)) [Q.IsPrime] (hQ : Q.height = 1) :
    IsLocalRing.maximalIdeal (Localization.AtPrime Q) ≠ ⊥ := by
  intro hmax
  have hunder : (IsLocalRing.maximalIdeal (Localization.AtPrime Q)).under (normalizationRing A) = Q :=
    Localization.AtPrime.under_maximalIdeal
  rw [hmax] at hunder
  have hbot : (⊥ : Ideal (Localization.AtPrime Q)).under (normalizationRing A) = ⊥ :=
    Ideal.comap_bot_of_injective (algebraMap (normalizationRing A) (Localization.AtPrime Q))
      (FaithfulSMul.algebraMap_injective _ _)
  exact Ideal.ne_bot_of_height_eq_one hQ (hunder.symm.trans hbot)

variable {k : Type u} [Field k] [CharZero k] [Algebra k A]

/-- The actual height-one normalization stalk bounds arbitrary original
normalized projective-chart sections by the full-fiber hypersurface
degree. Only the original projection coordinates, their independent
pair and transcendental residue are supplied; every scalar action,
normal local model, finite field bound and section integrality is derived. -/
theorem canonical_normalization_original_section_order_le_hypersurface_degree
    (Q : Ideal (normalizationRing A)) [Q.IsPrime] (hQ : Q.height = 1)
    (u w : A) (hu : Transcendental k (IsLocalRing.residue (Localization.AtPrime Q)
      (algebraMap A (Localization.AtPrime Q) u)))
    (hind : AlgebraicIndependent k ![u, w])
    (x : Fin 4 → FractionRing A) (sectionValue : ProjectiveNormalizedSection (k := k) x)
    (s : Fin 4 ≃ Option (Fin 3)) (hbase : x (s.symm none) ≠ 0)
    (hfield : IntermediateField.adjoin k
      (Set.range (fun j => x (s.symm (some j)) / x (s.symm none))) = ⊤)
    (T : (Fin 3 → k) ≃ₗ[k] (Fin 3 → k)) (v : FractionRing A)
    (hcoordinates : linearProjectionCoordinate T
      (fun j => x (s.symm (some j)) / x (s.symm none)) =
      ![v, algebraMap A (FractionRing A) w, algebraMap A (FractionRing A) u])
    (g : MvPolynomial (Option (Fin 2)) k) (hg : g ≠ 0)
    (hfull : g.degreeOf none = g.totalDegree)
    (hrelation : MvPolynomial.aeval (fun i : Option (Fin 2) => i.elim v
      (fun j => ![algebraMap A (FractionRing A) w, algebraMap A (FractionRing A) u] j)) g = 0)
    (b : Localization.AtPrime Q) (hb : b ≠ 0)
    (a : ℕ) (horder : b ∈ (IsLocalRing.maximalIdeal (Localization.AtPrime Q)) ^ a) :
    let : Algebra (Localization.AtPrime Q) (FractionRing A) := normalizationPrimeFractionAlgebra Q
    (sectionValue.coefficient (s.symm none) : FractionRing A) =
      algebraMap (Localization.AtPrime Q) (FractionRing A) b → a ≤ g.totalDegree := by
  let B := Localization.AtPrime Q
  let L := FractionRing A
  let : Algebra B L := normalizationPrimeFractionAlgebra Q
  let : IsFractionRing B L := normalizationPrimeFractionAlgebra_isFractionRing Q
  let : IsScalarTower A B L := normalizationPrimeFractionAlgebra_source_scalarTower Q
  let : IsScalarTower k B L := normalizationPrimeFractionAlgebra_base_scalarTower Q
  let : IsIntegrallyClosed B := normalization_prime_local_isIntegrallyClosed Q
  change (sectionValue.coefficient (s.symm none) : L) = algebraMap B L b → a ≤ g.totalDegree
  intro hvalue
  have hp : AlgebraicIndependent k ![algebraMap B L (algebraMap A B u),
      algebraMap B L (algebraMap A B w)] := by
    simp only [← IsScalarTower.algebraMap_apply A B L]
    have hm : AlgebraicIndependent k (fun i => algebraMap A L (![u, w] i)) :=
      hind.map' (f := IsScalarTower.toAlgHom k A L) (IsFractionRing.injective A L)
    have heq : (fun i => algebraMap A L (![u, w] i)) =
        ![algebraMap A L u, algebraMap A L w] := by
      funext i
      fin_cases i <;> rfl
    exact Eq.mp (congrArg (fun f : Fin 2 → L => AlgebraicIndependent k f) heq) hm
  have hcoordinates' : linearProjectionCoordinate T
      (fun j => x (s.symm (some j)) / x (s.symm none)) =
      ![v, algebraMap B L (algebraMap A B w), algebraMap B L (algebraMap A B u)] := by
    simpa only [← IsScalarTower.algebraMap_apply A B L] using hcoordinates
  have hrelation' : MvPolynomial.aeval (fun i : Option (Fin 2) => i.elim v
      (fun j => ![algebraMap B L (algebraMap A B w), algebraMap B L (algebraMap A B u)] j)) g = 0 := by
    simpa only [← IsScalarTower.algebraMap_apply A B L] using hrelation
  exact original_chart_residue_projection_section_order_le_hypersurface_degree
    (normalization_prime_local_maximalIdeal_ne_bot Q hQ)
    (algebraMap A B u) (algebraMap A B w) hu hp x sectionValue s hbase hfield
    T v hcoordinates' g hg hfull hrelation' b hb hvalue a horder

end DimensionFourDependence
