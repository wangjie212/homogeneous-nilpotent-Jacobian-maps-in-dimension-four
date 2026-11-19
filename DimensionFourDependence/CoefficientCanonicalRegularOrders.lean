import DimensionFourDependence.CoefficientCanonicalSourceOrders
import DimensionFourDependence.NormalizationCanonicalOrders

/-! # Exact canonical regular orders after finite coefficient extension

The constructed coefficient-normalization model preserves the powers
of the maximal ideal for the actual canonical source-local map.
-/

namespace DimensionFourDependence

open scoped TensorProduct

set_option synthInstance.maxHeartbeats 100000
set_option maxHeartbeats 2000000

/-- Exact regular orders for a specified canonical map between prime
localizations. Keeping this statement named avoids expanding local
ideal structures when applying it to concrete projective source fields. -/
noncomputable def CanonicalRegularSourceOrderComparison
    {R T : Type*} [CommRing R] [CommRing T]
    (Q : Ideal R) [Q.IsPrime] (q : Ideal T) [q.IsPrime]
    (f : R →+* T) (hf : Q = q.comap f) : Prop :=
  ∀ (x : Localization.AtPrime Q) (a : ℕ),
    Localization.localRingHom Q q f hf x ∈
      (IsLocalRing.maximalIdeal (Localization.AtPrime q)) ^ a ↔
        x ∈ (IsLocalRing.maximalIdeal (Localization.AtPrime Q)) ^ a

/-- The exact canonical comparison on an original ring element can
be stated using its original value, with no localization-map expression. -/
theorem canonicalRegularSourceOrderComparison_algebraMap
    {R T : Type*} [CommRing R] [CommRing T]
    (Q : Ideal R) [Q.IsPrime] (q : Ideal T) [q.IsPrime]
    (f : R →+* T) (hf : Q = q.comap f)
    (horder : CanonicalRegularSourceOrderComparison Q q f hf) (r : R) (a : ℕ) :
    algebraMap T (Localization.AtPrime q) (f r) ∈
        (IsLocalRing.maximalIdeal (Localization.AtPrime q)) ^ a ↔
      algebraMap R (Localization.AtPrime Q) r ∈
        (IsLocalRing.maximalIdeal (Localization.AtPrime Q)) ^ a := by
  have h := horder (algebraMap R (Localization.AtPrime Q) r) a
  rwa [Localization.localRingHom_to_map] at h

variable {R k S F E : Type*} [CommRing R] [IsDomain R]
  [Field k] [CharZero k] [CommRing S] [Field F] [Field E]
  [Algebra R S] [Algebra k S] [Algebra k F] [Algebra k E]
  [Module.Finite k E]
  (Q : Ideal R) [Q.IsPrime]
  [IsDiscreteValuationRing (Localization.AtPrime Q)]
  [Algebra k (Localization.AtPrime Q)] [Algebra S (Localization.AtPrime Q)]
  [IsScalarTower R S (Localization.AtPrime Q)]
  [IsScalarTower k S (Localization.AtPrime Q)]
  [FaithfulSMul S (Localization.AtPrime Q)]
  [Algebra (Localization.AtPrime Q) F]
  [IsScalarTower k (Localization.AtPrime Q) F]
  [IsFractionRing (Localization.AtPrime Q) F]
  [IsLocalization (Algebra.algebraMapSubmonoid S Q.primeCompl) (Localization.AtPrime Q)]

local notation "O₀" => Localization.AtPrime Q
local notation "Sₑ" => S ⊗[k] E
local notation "Aₑ" => O₀ ⊗[k] E
local notation "M₀" => Algebra.algebraMapSubmonoid S Q.primeCompl
local notation "Mₑ" => Algebra.algebraMapSubmonoid Sₑ M₀

/-- Every given canonical normalization prime has the same regular
orders through its canonical map from the original source DVR. -/
theorem coefficient_canonical_normalization_regular_orders
    (hclosed : algebraicClosure k F = ⊥) :
    letI : Algebra R Sₑ := sourceCoefficientExtensionAlgebra (R := R) (k := k) (S := S) (E := E)
    letI : Algebra R (normalizationRing Sₑ) :=
      ((algebraMap Sₑ (normalizationRing Sₑ)).comp (algebraMap R Sₑ)).toAlgebra
    ∀ (q : Ideal (normalizationRing Sₑ)) [q.IsPrime] [q.LiesOver Q],
      CanonicalRegularSourceOrderComparison Q q
        (algebraMap R (normalizationRing Sₑ)) (Ideal.over_def q Q) := by
  let : IsDomain Aₑ := relatively_closed_local_ring_base_change_isDomain hclosed
  let : IsDedekindDomain Aₑ := relatively_closed_dvr_base_change_dedekind hclosed
  let : Algebra.Etale O₀ Aₑ := (finite_coefficient_base_change_etale (k := k) (A := O₀) (E := E)).2
  let : IsDomain Sₑ := Function.Injective.isDomain
    (coefficientLocalizationHom (k := k) (S := S) (A := O₀) (E := E)) coefficientLocalizationHom_injective
  let : Algebra Sₑ Aₑ :=
    (coefficientLocalizationHom (k := k) (S := S) (A := O₀) (E := E)).toRingHom.toAlgebra
  let : FaithfulSMul Sₑ Aₑ :=
    (faithfulSMul_iff_algebraMap_injective _ _).mpr coefficientLocalizationHom_injective
  let : IsLocalization Mₑ Aₑ := coefficient_localization_isLocalization M₀
  let : Algebra Aₑ (FractionRing Sₑ) := coordinateLocalizationCanonicalFractionAlgebra (A := Aₑ) Mₑ
  let : IsScalarTower Sₑ Aₑ (FractionRing Sₑ) := coordinateLocalizationCanonicalFraction_scalarTower Mₑ
  let : IsFractionRing Aₑ (FractionRing Sₑ) := coordinateLocalizationCanonicalFraction_isFractionRing Mₑ
  let : Algebra R Sₑ := sourceCoefficientExtensionAlgebra (R := R) (k := k) (S := S) (E := E)
  let : Algebra R Aₑ := sourceCoefficientExtensionAlgebra (R := R) (k := k) (S := O₀) (E := E)
  let : IsScalarTower R O₀ Aₑ := sourceCoefficientExtension_scalarTower
  have hmodel := coefficient_canonical_normalization_source_orders
    (R := R) (k := k) (S := S) (A := O₀) (F := F) (E := E) hclosed Q
  exact normalization_local_canonical_regular_orders (S := Sₑ) (B := Aₑ)
    (F := FractionRing Sₑ) (L := F) Q hmodel

/-- The canonical rational source map extends the actual local map
and preserves every normalized discrete valuation after coefficient extension. -/
theorem coefficient_canonical_normalization_rational_orders
    (hclosed : algebraicClosure k F = ⊥) :
    letI : IsDomain Aₑ := relatively_closed_local_ring_base_change_isDomain hclosed
    letI : IsDomain Sₑ := Function.Injective.isDomain
      (coefficientLocalizationHom (k := k) (S := S) (A := O₀) (E := E)) coefficientLocalizationHom_injective
    letI : Algebra R Sₑ := sourceCoefficientExtensionAlgebra (R := R) (k := k) (S := S) (E := E)
    letI : Algebra R (normalizationRing Sₑ) :=
      ((algebraMap Sₑ (normalizationRing Sₑ)).comp (algebraMap R Sₑ)).toAlgebra
    ∀ (q : Ideal (normalizationRing Sₑ)) [q.IsPrime] [q.LiesOver Q],
      ∃ hdvr : IsDiscreteValuationRing (Localization.AtPrime q),
        letI := hdvr
        letI : Algebra (Localization.AtPrime q) (FractionRing (Localization.AtPrime q)) :=
          OreLocalization.instAlgebra
        ∃ j : F →+* FractionRing (Localization.AtPrime q),
          (∀ x : O₀,
            j (algebraMap O₀ F x) =
              algebraMap (Localization.AtPrime q) (FractionRing (Localization.AtPrime q))
                (Localization.localRingHom Q q (algebraMap R (normalizationRing Sₑ))
                  (Ideal.over_def q Q) x)) ∧
          let v : IsDedekindDomain.HeightOneSpectrum O₀ :=
            ⟨IsLocalRing.maximalIdeal _, inferInstance, IsDiscreteValuationRing.not_a_field O₀⟩
          let w : IsDedekindDomain.HeightOneSpectrum (Localization.AtPrime q) :=
            ⟨IsLocalRing.maximalIdeal _, inferInstance,
              IsDiscreteValuationRing.not_a_field (Localization.AtPrime q)⟩
          ∀ x : F, v.valuation F x = w.valuation (FractionRing (Localization.AtPrime q)) (j x) := by
  let : IsDomain Aₑ := relatively_closed_local_ring_base_change_isDomain hclosed
  let : IsDedekindDomain Aₑ := relatively_closed_dvr_base_change_dedekind hclosed
  let : Algebra.Etale O₀ Aₑ := (finite_coefficient_base_change_etale (k := k) (A := O₀) (E := E)).2
  let : IsDomain Sₑ := Function.Injective.isDomain
    (coefficientLocalizationHom (k := k) (S := S) (A := O₀) (E := E)) coefficientLocalizationHom_injective
  let : Algebra Sₑ Aₑ :=
    (coefficientLocalizationHom (k := k) (S := S) (A := O₀) (E := E)).toRingHom.toAlgebra
  let : FaithfulSMul Sₑ Aₑ :=
    (faithfulSMul_iff_algebraMap_injective _ _).mpr coefficientLocalizationHom_injective
  let : IsLocalization Mₑ Aₑ := coefficient_localization_isLocalization M₀
  let : Algebra Aₑ (FractionRing Sₑ) := coordinateLocalizationCanonicalFractionAlgebra (A := Aₑ) Mₑ
  let : IsScalarTower Sₑ Aₑ (FractionRing Sₑ) := coordinateLocalizationCanonicalFraction_scalarTower Mₑ
  let : IsFractionRing Aₑ (FractionRing Sₑ) := coordinateLocalizationCanonicalFraction_isFractionRing Mₑ
  let : Algebra R Sₑ := sourceCoefficientExtensionAlgebra (R := R) (k := k) (S := S) (E := E)
  let : Algebra R Aₑ := sourceCoefficientExtensionAlgebra (R := R) (k := k) (S := O₀) (E := E)
  let : IsScalarTower R O₀ Aₑ := sourceCoefficientExtension_scalarTower
  have hmodel := coefficient_canonical_normalization_source_orders
    (R := R) (k := k) (S := S) (A := O₀) (F := F) (E := E) hclosed Q
  exact normalization_local_canonical_rational_orders (S := Sₑ) (B := Aₑ)
    (F := FractionRing Sₑ) (L := F) Q hmodel

end DimensionFourDependence
