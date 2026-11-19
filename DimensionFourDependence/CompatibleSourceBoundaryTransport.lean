import DimensionFourDependence.ConeFieldExtension
import DimensionFourDependence.ProjectivePrimeBaseExtension

/-! # The same embedded-source boundary is a boundary of the original coefficient-field fiber -/

namespace DimensionFourDependence

open MvPolynomial

attribute [local instance] MvPolynomial.gradedAlgebra

set_option maxHeartbeats 1500000
set_option synthInstance.maxHeartbeats 100000

/-- Every boundary point of a compatibly embedded original source
is an actual extension-valued point of the original coefficient-field
closure. The coefficients and original coordinates are transported
through the same maps, with no new boundary point chosen. -/
theorem compatible_source_boundary_mem_original_coefficient_closure
    {L S B Z : Type*} [Field L] [Field S] [Field B] [Field Z]
    [Algebra L S] [Algebra B Z] {n : ℕ}
    (f : S →+* Z) (g : L →+* B) (x : Fin n → S) (y : Fin n → Z)
    (hcoeff : ∀ l : L, f (algebraMap L S l) = algebraMap B Z (g l))
    (hcoords : ∀ i, f (x i) = y i) :
    letI : Algebra L B := g.toAlgebra
    ∀ (b : Option (Fin n) → B) (hb : b ≠ 0),
      projectiveFieldPoint (E := B) b hb ∈ projectiveClosureSet (L := B) y →
      projectiveFieldPoint (E := L) b hb ∈ projectiveClosureSet (L := L) x := by
  letI : Algebra L B := g.toAlgebra
  intro b hb hboundary
  letI : Algebra L Z := ((algebraMap B Z).comp g).toAlgebra
  letI : IsScalarTower L B Z := IsScalarTower.of_algebraMap_eq' rfl
  let fL : S →ₐ[L] Z := { f with commutes' := hcoeff }
  have hrel : extendCoefficientIdeal B (fiberVanishingIdeal (L := L) x) ≤
      fiberVanishingIdeal (L := B) y := by
    apply Ideal.map_le_iff_le_comap.mpr
    intro P hP
    change aeval (R := B) y (MvPolynomial.map (algebraMap L B) P) = 0
    rw [aeval_map_coefficients]
    have he := comp_aeval_apply x fL P
    rw [show (fun i => fL (x i)) = y from funext hcoords] at he
    rw [← he]
    simpa only [map_zero] using congrArg fL hP
  have hcone := projectiveConeIdeal_extended_le x y hrel
  apply projective_field_point_of_extended_cone_relations_mem_original_closure (F := B) x b hb
  apply hcone.trans
  rw [projectiveClosureSet_eq_zeroLocus_cone] at hboundary
  exact hboundary

end DimensionFourDependence
