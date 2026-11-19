import DimensionFourDependence.ProjectiveBoundaryCoefficientComponent
import DimensionFourDependence.HomogenizeChart
import DimensionFourDependence.DehomogenizedBaseChange

/-! # The chosen extended projective component retains exact affine source relations -/

namespace DimensionFourDependence

open MvPolynomial

attribute [local instance] MvPolynomial.gradedAlgebra MvPolynomial.algebraMvPolynomial

set_option maxHeartbeats 3000000
set_option synthInstance.maxHeartbeats 100000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {C A G : Type*} [Field C] [Field A] [Field G] [Algebra C A] [Algebra C G] {n : ℕ}

/-- Exact contraction of the original homogeneous cone prime gives
exact contraction of all affine relations of the chosen component's
own normalized source coordinates. Homogenization retains every
original polynomial, not just homogeneous equations. -/
theorem extended_projective_chart_coordinates_contract_affine_relations
    (v : Fin n → G)
    (q : ProjectiveSpectrum (homogeneousSubmodule (Option (Fin n)) A))
    (hqa : X none ∉ q.asHomogeneousIdeal)
    (hcontract : q.asHomogeneousIdeal.toIdeal.comap (MvPolynomial.map (algebraMap C A)) =
      projectiveConeIdeal (L := C) v) :
    (fiberVanishingIdeal (L := A) (fun i => projectivePrimeRatioCoordinate q none (some i))).comap
      (MvPolynomial.map (algebraMap C A)) = fiberVanishingIdeal (L := C) v := by
  let x := fun i => projectivePrimeRatioCoordinate q none (some i)
  have hcoords : (fun j : Option (Fin n) => j.elim 1 x) = projectivePrimeRatioCoordinate q none := by
    funext j
    cases j with
    | none => exact (projectivePrimeRatioCoordinate_self q none hqa).symm
    | some i => rfl
  ext P
  let H := projectiveHomogenize P P.totalDegree
  have hH : H.IsHomogeneous P.totalDegree := projectiveHomogenize_isHomogeneous P _ le_rfl
  have heval : aeval (R := A) (projectivePrimeRatioCoordinate q none)
      (MvPolynomial.map (algebraMap C A) H) = aeval x (MvPolynomial.map (algebraMap C A) P) := by
    rw [← hcoords, aeval_projectiveDehomogenize, projectiveDehomogenize_map_coefficients]
    rw [show projectiveDehomogenize H = P from projectiveDehomogenize_homogenize P _]
  have hcone : H ∈ projectiveConeIdeal (L := C) v ↔ aeval v P = 0 := by
    rw [projectiveConeIdeal_mem_of_isHomogeneous v hH]
    change aeval (fun j : Option (Fin n) => j.elim 1 v) (projectiveHomogenize P P.totalDegree) = 0 ↔ _
    rw [projectiveHomogenize_aeval_chart]
  change aeval x (MvPolynomial.map (algebraMap C A) P) = 0 ↔ aeval v P = 0
  rw [← heval, projectivePrimeRatioCoordinate_homogeneous_zero_iff q none hqa _ (hH.map _)]
  change H ∈ q.asHomogeneousIdeal.toIdeal.comap (MvPolynomial.map (algebraMap C A)) ↔ _
  rw [hcontract]
  exact hcone

/-- Over an algebraic coefficient extension, these actual affine
coordinates define a minimal component of the extended original affine
relation prime, with no extra source relations supplied as assumptions. -/
theorem extended_projective_chart_coordinates_form_affine_component
    [Algebra.IsAlgebraic C A] (v : Fin n → G)
    (q : ProjectiveSpectrum (homogeneousSubmodule (Option (Fin n)) A))
    (hqa : X none ∉ q.asHomogeneousIdeal)
    (hcontract : q.asHomogeneousIdeal.toIdeal.comap (MvPolynomial.map (algebraMap C A)) =
      projectiveConeIdeal (L := C) v) :
    fiberVanishingIdeal (L := A) (fun i => projectivePrimeRatioCoordinate q none (some i)) ∈
      (extendCoefficientIdeal A (fiberVanishingIdeal (L := C) v)).minimalPrimes := by
  apply prime_minimal_over_integral_extension (MvPolynomial.map (algebraMap C A)) _ _ _
    (extended_projective_chart_coordinates_contract_affine_relations v q hqa hcontract)
  rw [← MvPolynomial.algebraMap_def]
  exact algebraMap_isIntegral_iff.mpr inferInstance

end DimensionFourDependence
