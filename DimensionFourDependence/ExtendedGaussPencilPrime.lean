import DimensionFourDependence.ClosedGaussPencilScheme
import DimensionFourDependence.ComponentGenericPoint

/-! # The actual closed Gauss pencil prime after algebraic coefficient extension

The extended homogeneous ideal is prime, contracts to exactly the
original source ideal, and excludes every original source coordinate.
It therefore defines the actual extended projective generic point.
-/

namespace DimensionFourDependence

open MvPolynomial
open scoped TensorProduct

attribute [local instance] MvPolynomial.gradedAlgebra

universe u

set_option synthInstance.maxHeartbeats 100000
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {K : Type u} [Field K] [CharZero K]
  (H : Fin 4 → MvPolynomial (Fin 4) K) (I : ImageRelationWitness H)
  (E : Type u) [Field E] [Algebra (closedGaussParameterField H I) E]
  [Algebra.IsAlgebraic (closedGaussParameterField H I) E]

local notation "C₀" => closedGaussParameterField H I
local notation "J₀" => fiberVanishingIdeal (L := C₀) (rationalCoordinate (K := K) (n := 4))

/-- The original homogeneous source prime extended to the actual coefficient field. -/
noncomputable def extendedClosedGaussPencilIdeal : Ideal (MvPolynomial (Fin 4) E) :=
  extendCoefficientIdeal E J₀

set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
/-- Algebraic coefficient extension leaves the full original pencil quotient a domain. -/
theorem extendedClosedGaussPencilIdeal_quotient_isDomain :
    IsDomain (MvPolynomial (Fin 4) E ⧸ extendedClosedGaussPencilIdeal H I E) := by
  let : IsDomain ((MvPolynomial (Fin 4) C₀ ⧸ J₀) ⊗[C₀] E) :=
    actual_closed_gauss_coordinate_quotient_algebraic_base_change_isDomain H I E
  let c := Algebra.TensorProduct.comm C₀ E (MvPolynomial (Fin 4) C₀ ⧸ J₀)
  let : IsDomain (E ⊗[C₀] (MvPolynomial (Fin 4) C₀ ⧸ J₀)) :=
    Function.Injective.isDomain c c.injective
  let b := polynomialQuotientBaseChangeEquiv E J₀
  exact Function.Injective.isDomain b.symm b.symm.injective

/-- The actual extended source relation ideal is prime. -/
@[instance] theorem extendedClosedGaussPencilIdeal_isPrime :
    (extendedClosedGaussPencilIdeal H I E).IsPrime :=
  (Ideal.Quotient.isDomain_iff_prime _).mp (extendedClosedGaussPencilIdeal_quotient_isDomain H I E)

/-- Its contraction has exactly the original source relations. -/
theorem extendedClosedGaussPencilIdeal_comap :
    (extendedClosedGaussPencilIdeal H I E).comap (MvPolynomial.map (algebraMap C₀ E)) = J₀ := by
  apply minimalPrime_extended_coefficients_comap E J₀ (extendedClosedGaussPencilIdeal H I E)
  change extendedClosedGaussPencilIdeal H I E ∈ (extendedClosedGaussPencilIdeal H I E).minimalPrimes
  rw [Ideal.minimalPrimes_eq_subsingleton_self]
  exact Set.mem_singleton _

/-- Every original homogeneous source coordinate remains nonzero on the extended pencil. -/
theorem extendedClosedGaussPencilIdeal_X_not_mem (a : Fin 4) :
    X a ∉ extendedClosedGaussPencilIdeal H I E := by
  intro hx
  have hm : (X a : MvPolynomial (Fin 4) C₀) ∈
      (extendedClosedGaussPencilIdeal H I E).comap (MvPolynomial.map (algebraMap C₀ E)) := by
    simpa only [Ideal.mem_comap, MvPolynomial.map_X] using hx
  rw [extendedClosedGaussPencilIdeal_comap] at hm
  change aeval (rationalCoordinate (K := K) (n := 4)) (X a) = 0 at hm
  rw [aeval_X] at hm
  apply (IsFractionRing.injective (MvPolynomial (Fin 4) K)
    (FractionRing (MvPolynomial (Fin 4) K))).ne (X_ne_zero a)
  simpa only [rationalCoordinate, map_zero] using hm

omit [Algebra.IsAlgebraic (closedGaussParameterField H I) E] in
/-- The actual extended prime is homogeneous in the original source variables. -/
theorem extendedClosedGaussPencilIdeal_isHomogeneous {d : ℕ} (hH : IsHomogMap H d)
    (e : RatFunc K ≃ₐ[K] C₀) :
    (extendedClosedGaussPencilIdeal H I E).IsHomogeneous (homogeneousSubmodule (Fin 4) E) :=
  extendCoefficientIdeal_isHomogeneous E J₀
    (actual_closed_gauss_pencil_relation_ideal_isHomogeneous H hH I e)

/-- The actual projective generic point after the algebraic coefficient extension. -/
noncomputable def extendedClosedGaussPencilGenericPoint {d : ℕ} (hH : IsHomogMap H d)
    (e : RatFunc K ≃ₐ[K] C₀) : ProjectiveSpectrum (homogeneousSubmodule (Fin 4) E) where
  asHomogeneousIdeal :=
    { toSubmodule := extendedClosedGaussPencilIdeal H I E
      is_homogeneous' := extendedClosedGaussPencilIdeal_isHomogeneous H I E hH e }
  isPrime := extendedClosedGaussPencilIdeal_isPrime H I E
  not_irrelevant_le := by
    intro hle
    exact extendedClosedGaussPencilIdeal_X_not_mem H I E 0
      (hle (HomogeneousIdeal.mem_irrelevant_of_mem _ (show 0 < (1 : ℕ) by omega)
        (isHomogeneous_X (R := E) (0 : Fin 4))))

end DimensionFourDependence
