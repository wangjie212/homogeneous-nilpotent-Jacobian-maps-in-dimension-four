import DimensionFourDependence.SourceCoefficientExtension
import DimensionFourDependence.NormalizationRing

/-! # Contracting a given extended normalization prime to the original chart

The prime of the original pencil coordinate ring used to construct the
horizontal parameter is the contraction of the given normalized prime.
It is not an independently assumed auxiliary prime.
-/

namespace DimensionFourDependence

open scoped TensorProduct

variable {R k S E : Type*} [CommRing R] [CommRing k] [CommRing S] [CommRing E]
  [Algebra R S] [Algebra k S] [Algebra k E] [IsDomain (S ⊗[k] E)]

omit [IsDomain (S ⊗[k] E)] in
/-- A given prime of the canonical coefficient-extended normalization
contracts to a prime above the same original source divisor. -/
theorem coefficient_normalization_prime_contraction (Q : Ideal R) :
    letI : Algebra R (S ⊗[k] E) := sourceCoefficientExtensionAlgebra (R := R) (k := k) (S := S) (E := E)
    letI : Algebra S (normalizationRing (S ⊗[k] E)) :=
      ((algebraMap (S ⊗[k] E) (normalizationRing (S ⊗[k] E))).comp
        (algebraMap S (S ⊗[k] E))).toAlgebra
    letI : Algebra R (normalizationRing (S ⊗[k] E)) :=
      ((algebraMap (S ⊗[k] E) (normalizationRing (S ⊗[k] E))).comp
        (algebraMap R (S ⊗[k] E))).toAlgebra
    ∀ (q : Ideal (normalizationRing (S ⊗[k] E))) [q.IsPrime] [q.LiesOver Q],
      (q.under S).LiesOver Q := by
  let : Algebra R (S ⊗[k] E) := sourceCoefficientExtensionAlgebra (R := R) (k := k) (S := S) (E := E)
  let : Algebra S (normalizationRing (S ⊗[k] E)) :=
    ((algebraMap (S ⊗[k] E) (normalizationRing (S ⊗[k] E))).comp
      (algebraMap S (S ⊗[k] E))).toAlgebra
  let : Algebra R (normalizationRing (S ⊗[k] E)) :=
    ((algebraMap (S ⊗[k] E) (normalizationRing (S ⊗[k] E))).comp
      (algebraMap R (S ⊗[k] E))).toAlgebra
  intro q hq hlie
  have hmaps : (algebraMap S (normalizationRing (S ⊗[k] E))).comp (algebraMap R S) =
      algebraMap R (normalizationRing (S ⊗[k] E)) := by
    ext r
    rfl
  apply (Ideal.liesOver_iff _ _).mpr
  change Q = (q.comap (algebraMap S (normalizationRing (S ⊗[k] E)))).comap (algebraMap R S)
  rw [Ideal.comap_comap, hmaps]
  exact Ideal.over_def q Q

end DimensionFourDependence
