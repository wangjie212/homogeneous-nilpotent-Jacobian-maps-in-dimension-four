import DimensionFourDependence.ClosedGaussCoordinateLocalRing
import DimensionFourDependence.CoefficientNormalizedLocalRing

/-! # Actual closed Gauss coordinate local rings over finite coefficient fields

The coordinate algebra, source divisor DVR, coefficient extension and
normalization maps all use their actual original-source realizations.
The tensor-product localization theorem identifies the extended
coordinate local ring, and its normalization, with the constructed
unramified extension of the source divisor DVR.
-/

namespace DimensionFourDependence

open scoped TensorProduct

set_option synthInstance.maxHeartbeats 100000
set_option maxHeartbeats 1000000

variable {K : Type*} [Field K]
  (H : Fin 4 → MvPolynomial (Fin 4) K) (I : ImageRelationWitness H)
  (Q : Ideal (MvPolynomial (Fin 4) K)) [Q.IsPrime]
  [Algebra (closedGaussParameterField H I) (Localization.AtPrime Q)]
  [IsScalarTower (closedGaussParameterField H I) (Localization.AtPrime Q)
    (FractionRing (MvPolynomial (Fin 4) K))]

local notation "C₀" => closedGaussParameterField H I
local notation "G₀" => closedGaussCoordinateAlgebra H I
local notation "A₀" => Localization.AtPrime Q
local notation "F₀" => FractionRing (MvPolynomial (Fin 4) K)

/-- After coefficient extension, the actual coordinate local ring at a
contracted prime is the corresponding localization of the extended
source divisor ring. -/
theorem actual_closed_gauss_extended_coordinate_source_localization
    (E : Type*) [CommRing E] [Algebra C₀ E]
    (P : Ideal (A₀ ⊗[C₀] E)) [P.IsPrime] :
    letI : Algebra G₀ A₀ := (closedGaussCoordinateLocalHom H I Q).toRingHom.toAlgebra
    letI : IsScalarTower C₀ G₀ A₀ := IsScalarTower.of_algebraMap_eq
      (fun c => ((closedGaussCoordinateLocalHom H I Q).commutes c).symm)
    letI : Algebra (G₀ ⊗[C₀] E) (A₀ ⊗[C₀] E) :=
      (coefficientLocalizationHom (k := C₀) (S := G₀) (A := A₀) (E := E)).toRingHom.toAlgebra
    IsLocalization.AtPrime (Localization.AtPrime P) (P.under (G₀ ⊗[C₀] E)) := by
  let : Algebra G₀ A₀ := (closedGaussCoordinateLocalHom H I Q).toRingHom.toAlgebra
  let : IsScalarTower C₀ G₀ A₀ := IsScalarTower.of_algebraMap_eq
    (fun c => ((closedGaussCoordinateLocalHom H I Q).commutes c).symm)
  let : Algebra (G₀ ⊗[C₀] E) (A₀ ⊗[C₀] E) :=
    (coefficientLocalizationHom (k := C₀) (S := G₀) (A := A₀) (E := E)).toRingHom.toAlgebra
  let : IsLocalization.AtPrime A₀ ((IsLocalRing.maximalIdeal A₀).under G₀) :=
    actual_closed_gauss_coordinate_source_localization H I Q
  exact coefficient_localization_atPrime ((IsLocalRing.maximalIdeal A₀).under G₀).primeCompl P

variable [CharZero K]

/-- The actual coordinate normalization after finite coefficient
extension has the same local ring as the unramified source divisor
extension. The normalization prime and every algebra map are constructed
from their original source inclusions. -/
theorem actual_closed_gauss_extended_coordinate_normalization_source_localization
    (f : MvPolynomial (Fin 4) K) (hf : Prime f) (hQ : Q = Ideal.span {f})
    (E : Type*) [Field E] [Algebra C₀ E] [Module.Finite C₀ E]
    (P : Ideal (A₀ ⊗[C₀] E)) [P.IsPrime] [P.LiesOver (IsLocalRing.maximalIdeal A₀)] :
    letI : CharZero C₀ := charZero_of_injective_algebraMap (algebraMap K C₀).injective
    letI : IsDiscreteValuationRing A₀ := principal_prime_localization_isDVR Q f hf hQ
    letI : Algebra G₀ A₀ := (closedGaussCoordinateLocalHom H I Q).toRingHom.toAlgebra
    letI : IsScalarTower C₀ G₀ A₀ := IsScalarTower.of_algebraMap_eq
      (fun c => ((closedGaussCoordinateLocalHom H I Q).commutes c).symm)
    CoefficientNormalizationLocalRing (k := C₀) (S := G₀) (A := A₀) (F := F₀)
      (closedGaussParameterField_relatively_closed H I) P := by
  let : CharZero C₀ := charZero_of_injective_algebraMap (algebraMap K C₀).injective
  let : IsDiscreteValuationRing A₀ := principal_prime_localization_isDVR Q f hf hQ
  let : Algebra G₀ A₀ := (closedGaussCoordinateLocalHom H I Q).toRingHom.toAlgebra
  let : IsScalarTower C₀ G₀ A₀ := IsScalarTower.of_algebraMap_eq
    (fun c => ((closedGaussCoordinateLocalHom H I Q).commutes c).symm)
  let : FaithfulSMul G₀ A₀ :=
    (faithfulSMul_iff_algebraMap_injective _ _).mpr (closedGaussCoordinateLocalHom_injective H I Q)
  let : IsLocalization.AtPrime A₀ ((IsLocalRing.maximalIdeal A₀).under G₀) :=
    actual_closed_gauss_coordinate_source_localization H I Q
  exact coefficient_normalization_source_localization
    (closedGaussParameterField_relatively_closed H I) ((IsLocalRing.maximalIdeal A₀).under G₀).primeCompl P

end DimensionFourDependence
