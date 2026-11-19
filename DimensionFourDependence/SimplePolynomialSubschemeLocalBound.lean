import DimensionFourDependence.RationalPointLocalQuotient
import DimensionFourDependence.RankOneBoundaryChart

/-! # Closed subschemes of the actual simple boundary intersection

Original polynomial equation membership constructs a canonical
surjective map between the actual origin localizations. The exact
simple-root intersection bound therefore applies to every containing
chart ideal, without assuming a surjective local map separately.
-/

namespace DimensionFourDependence

open MvPolynomial Module

variable {F : Type*} [Field F]

/-- The actual local ring of any polynomial ideal containing u^2,P
has dimension and length at most two at the original simple root. -/
theorem simple_polynomial_containing_ideal_origin_local_bound
    (P : MvPolynomial (Fin 2) F) (hP : aeval (fun _ : Fin 2 => (0 : F)) P = 0)
    (hPv : aeval (fun _ : Fin 2 => (0 : F)) (pderiv 1 P) ≠ 0)
    (I : Ideal (MvPolynomial (Fin 2) F))
    (hI : I ≤ RingHom.ker (aeval (fun _ : Fin 2 => (0 : F))).toRingHom)
    (hu2 : X 0 ^ 2 ∈ I) (hPI : P ∈ I) :
    let R := Localization.AtPrime (zeroPointQuotientPrime I hI)
    Module.Finite F R ∧ finrank F R ≤ 2 ∧ Module.length R R ≤ 2 := by
  have hJI : simplePolynomialIntersectionIdeal P ≤ I := by
    apply Ideal.span_le.mpr
    rintro q (rfl | rfl)
    · exact hu2
    · exact hPI
  let phi : simplePolynomialIntersectionLocalRing P hP →ₐ[F]
      Localization.AtPrime (zeroPointQuotientPrime I hI) :=
    zeroPointLocalQuotientHom (simplePolynomialIntersectionIdeal P) I
      (simplePolynomialIntersectionIdeal_origin P hP) hI hJI
  have hsurj : Function.Surjective phi :=
    zeroPointLocalQuotientHom_surjective (simplePolynomialIntersectionIdeal P) I
      (simplePolynomialIntersectionIdeal_origin P hP) hI hJI
  exact simple_polynomial_intersection_local_quotient_bound
    (B := Localization.AtPrime (zeroPointQuotientPrime I hI)) P hP hPv phi hsurj

/-- A chart ideal containing the exact original first and second
boundary equations inherits their local bound. The first scalar,
point prime, and local quotient map are all handled in the proof. -/
theorem boundary_equations_containing_ideal_origin_local_bound
    (Q P : MvPolynomial (Fin 2) F) (scalar : F) (hscalar : scalar ≠ 0)
    (hQ : Q = C scalar * X 0 ^ 2)
    (hP : aeval (fun _ : Fin 2 => (0 : F)) P = 0)
    (hPv : aeval (fun _ : Fin 2 => (0 : F)) (pderiv 1 P) ≠ 0)
    (I : Ideal (MvPolynomial (Fin 2) F))
    (hI : I ≤ RingHom.ker (aeval (fun _ : Fin 2 => (0 : F))).toRingHom)
    (hQI : Q ∈ I) (hPI : P ∈ I) :
    let R := Localization.AtPrime (zeroPointQuotientPrime I hI)
    Module.Finite F R ∧ finrank F R ≤ 2 ∧ Module.length R R ≤ 2 := by
  have hpair : Ideal.span ({Q, P} : Set (MvPolynomial (Fin 2) F)) ≤ I := by
    apply Ideal.span_le.mpr
    rintro q (rfl | rfl)
    · exact hQI
    · exact hPI
  have heq : Ideal.span ({Q, P} : Set (MvPolynomial (Fin 2) F)) = simplePolynomialIntersectionIdeal P := by
    rw [hQ]
    exact scaled_coordinate_square_pair_ideal scalar hscalar P
  rw [heq] at hpair
  exact simple_polynomial_containing_ideal_origin_local_bound P hP hPv I hI
    (hpair (Ideal.subset_span (by simp))) hPI

end DimensionFourDependence
