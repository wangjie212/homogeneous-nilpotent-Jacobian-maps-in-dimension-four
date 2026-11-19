import DimensionFourDependence.ValuationProjectiveBoundary
import DimensionFourDependence.BoundaryIsotropicEquations

/-! # The radial exclusion in valuation-residue coordinates

A normalized valuation residue represents a point on the original
projective closure. If it equals the generic radial output direction,
the checked exclusion of Section 3.1 applies, even with a larger residue field.
-/

namespace DimensionFourDependence

open MvPolynomial

attribute [local instance] MvPolynomial.gradedAlgebra

variable {K : Type*} [Field K] [CharZero K]

/-- No integral normalization of an actual generic component can reduce
to the radial generic output when the image is nonlinear. -/
theorem radial_generic_output_not_valuation_residue
    (H : Fin 4 → MvPolynomial (Fin 4) K) {d : ℕ} (hd : 0 < d) (hH : IsHomogMap H d)
    (hN : IsNilpotent (jac H)) (hrank : polyRank (jac H) = 3) (hind : ¬ ComponentsDependent H)
    (E : Type*) [Field E] [Algebra (polynomialOutputField H) E]
    [Algebra K E] [IsScalarTower K (polynomialOutputField H) E]
    (P : Ideal (MvPolynomial (Fin 4) E)) [P.IsPrime]
    (hP : P ∈ (extendCoefficientIdeal E (fiberVanishingIdeal
      (L := polynomialOutputField H) (rationalCoordinate (K := K) (n := 4)))).minimalPrimes)
    (V : ValuationSubring (FractionRing (MvPolynomial (Fin 4) E ⧸ P)))
    [Algebra E V] :
    let vGAlgebra : Algebra V (FractionRing (MvPolynomial (Fin 4) E ⧸ P)) := inferInstance
    letI : SMul V (FractionRing (MvPolynomial (Fin 4) E ⧸ P)) := vGAlgebra.toSMul
    ∀ [IsScalarTower E V (FractionRing (MvPolynomial (Fin 4) E ⧸ P))]
      (s : FractionRing (MvPolynomial (Fin 4) E ⧸ P)) (z : Option (Fin 4) → V),
      (∀ j, algebraMap V (FractionRing (MvPolynomial (Fin 4) E ⧸ P)) (z j) =
        s * j.elim 1 (primeQuotientCoordinate P)) →
      (∀ j, IsLocalRing.residue V (z j) =
        algebraMap E (IsLocalRing.ResidueField V) (radialGenericOutputVector H E j)) → False := by
  let vGAlgebra : Algebra V (FractionRing (MvPolynomial (Fin 4) E ⧸ P)) := inferInstance
  let : SMul V (FractionRing (MvPolynomial (Fin 4) E ⧸ P)) := vGAlgebra.toSMul
  dsimp only
  intro hTower s z hz hres
  let κ := IsLocalRing.ResidueField V
  let π : V →ₐ[E] κ := IsScalarTower.toAlgHom E V κ
  have hvec := radialGenericOutputVector_ne_zero H (rank_three_polynomial_map_ne_zero H hrank) E
  have hmap : (fun j => algebraMap E κ (radialGenericOutputVector H E j)) ≠ 0 := by
    intro he
    apply hvec
    funext j
    apply (algebraMap E κ).injective
    simpa only [map_zero, Pi.zero_apply] using congrFun he j
  have hfun : (fun j => π (z j)) = fun j => algebraMap E κ (radialGenericOutputVector H E j) := by
    funext j
    exact hres j
  have hnonzero : (fun j => π (z j)) ≠ 0 := by rw [hfun]; exact hmap
  have hpoint := residue_field_point_mem_projective_closure π
    (show Function.Injective (algebraMap V (FractionRing (MvPolynomial (Fin 4) E ⧸ P)))
      from Subtype.val_injective) (primeQuotientCoordinate P) s z hz hnonzero
  simp only [hfun, projectiveFieldPoint_map_eq _ hvec] at hpoint
  exact radial_generic_output_not_in_geometric_fiber_closure H hd hH hN hrank hind E P hP hpoint

end DimensionFourDependence
