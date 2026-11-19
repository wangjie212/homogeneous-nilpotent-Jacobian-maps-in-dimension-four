import DimensionFourDependence.CoefficientCanonicalSourceOrders
import DimensionFourDependence.ProjectiveNormalizationMultiplicity
import DimensionFourDependence.PrimeLocalOrderConsequences

/-! # Canonical finite-coefficient normalization orders and the original factor

All source-order comparison data is constructed from the coordinate
denominator localization and relative closedness. For the given prime
of the canonical extended normalization, the original homogeneous
section order bounds imply the original common-factor degree bound.
-/

namespace DimensionFourDependence

open scoped TensorProduct

set_option synthInstance.maxHeartbeats 100000
set_option maxHeartbeats 1000000

variable {K : Type*} [Field K] (s : Fin 4 ≃ Option (Fin 3))

local notation "R₄" => MvPolynomial (Fin 4) K
local notation "R₀" => projectiveCoordinateChartAlgebra (C := K)
  (rationalCoordinate (K := K) (n := 4)) (s.symm none)

variable (Q : Ideal (projectiveCoordinateChartAlgebra (C := K)
  (rationalCoordinate (K := K) (n := 4)) (s.symm none))) [Q.IsPrime]

local notation "O₀" => Localization.AtPrime Q

/-- Finite-coefficient canonical normalization orders of the actual
projective source sections force the original homogeneous factor power
and degree bound; the source-order comparison is proved, not assumed. -/
theorem coefficient_projective_normalization_common_factor_degree
    {k S L E : Type*} [Field k] [CharZero k] [CommRing S] [Field L] [Field E]
    [IsDiscreteValuationRing O₀] [Algebra R₀ S]
    [Algebra k S] [Algebra k O₀] [Algebra k L] [Algebra k E]
    [Algebra S O₀] [IsScalarTower R₀ S O₀] [IsScalarTower k S O₀] [FaithfulSMul S O₀]
    [Algebra O₀ L] [IsScalarTower k O₀ L] [IsFractionRing O₀ L] [Module.Finite k E]
    [IsLocalization (Algebra.algebraMapSubmonoid S Q.primeCompl) O₀]
    (hclosed : algebraicClosure k L = ⊥)
    (H P : Fin 4 → R₄) (g : R₄) {c d : ℕ}
    (hg : g ≠ 0) (hgh : g.IsHomogeneous c) (hP : IsHomogMap P d)
    (hprim : IsPrimitiveVec P) (hHP : H = fun i => g * P i)
    (δ : MvPolynomial (Fin 3) K) (hδ : Irreducible δ)
    (hQ : Q = Ideal.span {projectiveSourceFullChartCoordinateEquiv s δ}) (a : ℕ) :
    letI : Algebra R₀ (S ⊗[k] E) :=
      sourceCoefficientExtensionAlgebra (R := R₀) (k := k) (S := S) (E := E)
    letI : Algebra R₀ (normalizationRing (S ⊗[k] E)) :=
      ((algebraMap (S ⊗[k] E) (normalizationRing (S ⊗[k] E))).comp
        (algebraMap R₀ (S ⊗[k] E))).toAlgebra
    PrimesOverSourceOrdersImply (T := normalizationRing (S ⊗[k] E)) Q
      (fun i => projectiveSourceSectionHom s (H i)) a
      (projectiveSourceHomogeneousDivisor s δ ^ a ∣ g ∧
        a * δ.totalDegree ≤ g.totalDegree ∧ a ≤ g.totalDegree) := by
  let : FaithfulSMul O₀ L := (faithfulSMul_iff_algebraMap_injective _ _).mpr
    (IsFractionRing.injective O₀ L)
  let : CommRing (O₀ ⊗[k] E) :=
    Algebra.TensorProduct.instCommRing (R := k) (A := O₀) (B := E)
  let : IsDomain (O₀ ⊗[k] E) :=
    relatively_closed_local_ring_base_change_isDomain (k := k) (A := O₀) (F := L) (E := E) hclosed
  let : IsDedekindDomain (O₀ ⊗[k] E) :=
    relatively_closed_dvr_base_change_dedekind (k := k) (A := O₀) (F := L) (E := E) hclosed
  let : Algebra.Etale O₀ (O₀ ⊗[k] E) :=
    (finite_coefficient_base_change_etale (k := k) (A := O₀) (E := E)).2
  let : IsDomain (S ⊗[k] E) := Function.Injective.isDomain
    (coefficientLocalizationHom (k := k) (S := S) (A := O₀) (E := E)) coefficientLocalizationHom_injective
  let : Algebra (S ⊗[k] E) (O₀ ⊗[k] E) :=
    (coefficientLocalizationHom (k := k) (S := S) (A := O₀) (E := E)).toRingHom.toAlgebra
  let : FaithfulSMul (S ⊗[k] E) (O₀ ⊗[k] E) :=
    (faithfulSMul_iff_algebraMap_injective _ _).mpr coefficientLocalizationHom_injective
  let M := Algebra.algebraMapSubmonoid (S ⊗[k] E) (Algebra.algebraMapSubmonoid S Q.primeCompl)
  let : IsLocalization M (O₀ ⊗[k] E) :=
    coefficient_localization_isLocalization (k := k) (S := S) (A := O₀) (E := E)
      (Algebra.algebraMapSubmonoid S Q.primeCompl)
  let sourceFieldAction : Algebra (O₀ ⊗[k] E) (FractionRing (S ⊗[k] E)) :=
    coordinateLocalizationCanonicalFractionAlgebra (A := O₀ ⊗[k] E) M
  let : Algebra (O₀ ⊗[k] E) (FractionRing (S ⊗[k] E)) := sourceFieldAction
  let : SMul (O₀ ⊗[k] E) (FractionRing (S ⊗[k] E)) := sourceFieldAction.toSMul
  let : IsScalarTower (S ⊗[k] E) (O₀ ⊗[k] E) (FractionRing (S ⊗[k] E)) :=
    coordinateLocalizationCanonicalFraction_scalarTower (S := S ⊗[k] E) (A := O₀ ⊗[k] E) M
  let : IsFractionRing (O₀ ⊗[k] E) (FractionRing (S ⊗[k] E)) :=
    coordinateLocalizationCanonicalFraction_isFractionRing (S := S ⊗[k] E) (A := O₀ ⊗[k] E) M
  let : Algebra R₀ (S ⊗[k] E) :=
    sourceCoefficientExtensionAlgebra (R := R₀) (k := k) (S := S) (E := E)
  let : Algebra R₀ (O₀ ⊗[k] E) :=
    sourceCoefficientExtensionAlgebra (R := R₀) (k := k) (S := O₀) (E := E)
  let : IsScalarTower R₀ S (S ⊗[k] E) :=
    sourceCoefficientExtension_scalarTower (R := R₀) (k := k) (S := S) (E := E)
  let : IsScalarTower R₀ O₀ (O₀ ⊗[k] E) :=
    sourceCoefficientExtension_scalarTower (R := R₀) (k := k) (S := O₀) (E := E)
  let : IsScalarTower R₀ (S ⊗[k] E) (O₀ ⊗[k] E) :=
    coefficientLocalization_original_source_scalarTower (R := R₀) (k := k) (S := S) (A := O₀) (E := E)
  let : IsLocalization (Algebra.algebraMapSubmonoid (S ⊗[k] E) Q.primeCompl) (O₀ ⊗[k] E) := by
    rw [← Algebra.algebraMapSubmonoid_map_map (A := S) (B := S ⊗[k] E)]
    infer_instance
  have horders := normalization_local_source_orders
    (S := S ⊗[k] E) (O := O₀) (B := O₀ ⊗[k] E) (F := FractionRing (S ⊗[k] E)) (L := L) Q
  exact normalization_projective_section_orders_common_factor_degree s Q
    H P g hg hgh hP hprim hHP δ hδ hQ a horders

end DimensionFourDependence
