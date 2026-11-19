import DimensionFourDependence.ValuationResidueCoordinates
import DimensionFourDependence.ExtensionFieldProjectivePoint

/-! # Coordinate poles produce actual projective boundary points

The valuative construction lands in Mathlib's projective closure over
the original constants. It requires no identification of the residue field.
-/

namespace DimensionFourDependence

open MvPolynomial

attribute [local instance] MvPolynomial.gradedAlgebra

variable {E F : Type*} [Field E] [Field F] [Algebra E F] {n : ℕ}

/-- A coordinate pole determines a point of the actual projective
closure on the infinity hyperplane. -/
theorem coordinate_pole_has_projective_boundary
    (V : ValuationSubring F) (hV : ∀ c : E, algebraMap E F c ∈ V)
    (x : Fin n → F) (i : Fin n) (hi : 1 < V.valuation (x i)) :
    ∃ p : ProjectiveSpectrum (homogeneousSubmodule (Option (Fin n)) E),
      p ∈ projectiveClosureSet (L := E) x ∧
      p ∈ ProjectiveSpectrum.zeroLocus (homogeneousSubmodule (Option (Fin n)) E) {X none} := by
  let : Algebra E V := valuationConstantAlgebra V hV
  let : IsScalarTower E V F := valuationConstantScalarTower V hV
  let κ := IsLocalRing.ResidueField V
  let π : V →ₐ[E] κ := IsScalarTower.toAlgHom E V κ
  obtain ⟨k, s, z, hz0, hz, hr0, hrk⟩ := exists_valuation_infinity_coordinates V x i hi
  have hres : (fun j => π (z j)) ≠ 0 := by
    intro he
    have hek := congrFun he (some k)
    change IsLocalRing.residue V (z (some k)) = 0 at hek
    exact one_ne_zero (hrk.symm.trans hek)
  let p := projectiveFieldPoint (E := E) (fun j => π (z j)) hres
  refine ⟨p, ?_, ?_⟩
  · apply residue_field_point_mem_projective_closure π
      (show Function.Injective (algebraMap V F) from Subtype.val_injective) x s z _ hres
    intro j
    cases j
    · change (z none : F) = s * 1
      simpa only [mul_one] using hz0
    · change (z (some _) : F) = s * _
      exact hz _
  · intro P hP
    rw [Set.mem_singleton_iff] at hP
    subst P
    change projectiveFieldPointMap (E := E) (fun j => π (z j)) (X none) = 0
    rw [projectiveFieldPointMap_homogeneous _ (isHomogeneous_X (R := E) none),
      Polynomial.monomial_eq_zero_iff, aeval_X]
    exact hr0

/-- A nonscalar coordinate over algebraically closed constants gives an
actual point at infinity of its projective closure. -/
theorem nonscalar_coordinate_has_projective_boundary [IsAlgClosed E]
    (x : Fin n → F) (i : Fin n) (hi : ¬ ∃ c : E, algebraMap E F c = x i) :
    ∃ p : ProjectiveSpectrum (homogeneousSubmodule (Option (Fin n)) E),
      p ∈ projectiveClosureSet (L := E) x ∧
      p ∈ ProjectiveSpectrum.zeroLocus (homogeneousSubmodule (Option (Fin n)) E) {X none} := by
  obtain ⟨V, hV, hpole⟩ := nonscalar_has_valuation_pole (x i) hi
  exact coordinate_pole_has_projective_boundary V hV x i hpole

end DimensionFourDependence
