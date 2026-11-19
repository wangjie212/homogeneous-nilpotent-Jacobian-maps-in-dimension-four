import DimensionFourDependence.HomogeneousCoefficientComponents
import DimensionFourDependence.OriginalClosureInfinitySupport
import DimensionFourDependence.HyperplaneAffineFiberBranch

/-! # A rational boundary point lies on an actual component after coefficient extension -/

namespace DimensionFourDependence

open MvPolynomial Topology

attribute [local instance] MvPolynomial.gradedAlgebra MvPolynomial.algebraMvPolynomial

set_option maxHeartbeats 3000000
set_option synthInstance.maxHeartbeats 100000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- A field-valued projective point over that same field is the
actual original coordinate point, independently of its proof witness. -/
theorem projectiveFieldPoint_self_eq_coordinatePoint
    {A σ : Type*} [Field A] (b : σ → A) (hb : b ≠ 0) :
    projectiveFieldPoint (E := A) b hb = projectiveCoordinatePoint b hb := by
  simpa using (projectiveFieldPoint_map_eq (E := A) (κ := A) b hb (by simpa using hb))

variable {C A G σ : Type*} [Field C] [Field A] [Field G] [Algebra C A] [Algebra C G]

/-- Every rational original boundary point constructs an actual
minimal projective component through its specified extension. The
component retains the original cone prime as its exact contraction
and still meets the original affine chart. -/
theorem projective_rational_boundary_constructs_extended_projective_component
    (v : σ → G) (b : Option σ → C) (hb : b ≠ 0)
    (hboundary : projectiveCoordinatePoint b hb ∈ projectiveClosureSet (L := C) v) :
    ∃ hbA : (fun j => algebraMap C A (b j)) ≠ 0,
      ∃ q : ProjectiveSpectrum (homogeneousSubmodule (Option σ) A),
        q.asHomogeneousIdeal.toIdeal ∈
          (extendCoefficientIdeal A (projectiveConeIdeal (L := C) v)).minimalPrimes ∧
        q.asHomogeneousIdeal.toIdeal.comap (MvPolynomial.map (algebraMap C A)) =
          projectiveConeIdeal (L := C) v ∧ X none ∉ q.asHomogeneousIdeal ∧
        q ⤳ projectiveCoordinatePoint (fun j => algebraMap C A (b j)) hbA := by
  have hbA : (fun j => algebraMap C A (b j)) ≠ 0 :=
    projective_coordinate_map_ne_zero (Algebra.ofId C A) b hb
  have hpoint : projectiveFieldPoint (E := C) (fun j => algebraMap C A (b j)) hbA ∈
      projectiveClosureSet (L := C) v := by
    rw [projectiveFieldPoint_map_eq b hb hbA]
    exact hboundary
  let z := projectiveFieldPoint (E := A) (fun j => algebraMap C A (b j)) hbA
  have hIle : extendCoefficientIdeal A (projectiveConeIdeal (L := C) v) ≤
      z.asHomogeneousIdeal.toIdeal := original_closure_point_contains_extended_cone v _ hbA hpoint
  letI : z.asHomogeneousIdeal.toIdeal.IsPrime := z.isPrime
  obtain ⟨Q, hQ, hQz⟩ := Ideal.exists_minimalPrimes_le hIle
  have hQhom := minimal_coefficient_component_isHomogeneous (projectiveConeIdeal (L := C) v)
    (projectiveConeIdeal_isHomogeneous v) Q hQ
  let q : ProjectiveSpectrum (homogeneousSubmodule (Option σ) A) :=
    { asHomogeneousIdeal := ⟨Q, hQhom⟩
      isPrime := hQ.isPrime
      not_irrelevant_le := fun h => z.not_irrelevant_le (h.trans hQz) }
  letI : (projectiveConeIdeal (L := C) v).IsPrime := projectiveConeIdeal_isPrime v
  have hcontract := minimalPrime_extended_coefficients_comap A (projectiveConeIdeal (L := C) v) Q hQ
  have hqa : X none ∉ q.asHomogeneousIdeal := by
    intro hx
    change X none ∈ Q at hx
    have hmem : X (none : Option σ) ∈ Q.comap (MvPolynomial.map (algebraMap C A)) := by
      change MvPolynomial.map (algebraMap C A) (X none) ∈ Q
      simpa only [MvPolynomial.map_X] using hx
    rw [hcontract] at hmem
    exact projectiveConeIdeal_X_none_not_mem v hmem
  refine ⟨hbA, q, hQ, hcontract, hqa, ?_⟩
  have hspec : q ⤳ z := specializes_iff_mem_closure.mpr
    ((ProjectiveSpectrum.le_iff_mem_closure (homogeneousSubmodule (Option σ) A) q z).mp hQz)
  simpa only [z, projectiveFieldPoint_self_eq_coordinatePoint] using hspec

/-- The selected extended component's own normalized affine source
coordinates have that same extended original boundary point in their
actual projective closure. -/
theorem projective_rational_boundary_constructs_extended_affine_coordinates
    (v : σ → G) (b : Option σ → C) (hb : b ≠ 0)
    (hboundary : projectiveCoordinatePoint b hb ∈ projectiveClosureSet (L := C) v) :
    ∃ hbA : (fun j => algebraMap C A (b j)) ≠ 0,
      ∃ q : ProjectiveSpectrum (homogeneousSubmodule (Option σ) A),
        q.asHomogeneousIdeal.toIdeal ∈
          (extendCoefficientIdeal A (projectiveConeIdeal (L := C) v)).minimalPrimes ∧
        q.asHomogeneousIdeal.toIdeal.comap (MvPolynomial.map (algebraMap C A)) =
          projectiveConeIdeal (L := C) v ∧
        ∃ hqa : X none ∉ q.asHomogeneousIdeal,
          projectiveCoordinatePoint (fun j => algebraMap C A (b j)) hbA ∈
            projectiveClosureSet (L := A)
              (fun i => projectivePrimeRatioCoordinate q none (some i)) := by
  obtain ⟨hbA, q, hQ, hcontract, hqa, hspec⟩ :=
    projective_rational_boundary_constructs_extended_projective_component (A := A) v b hb hboundary
  refine ⟨hbA, q, hQ, hcontract, hqa, ?_⟩
  change _ ∈ closure {projectiveClosureGenericPoint (L := A)
    (fun i => projectivePrimeRatioCoordinate q none (some i))}
  rw [projective_affine_chart_point_eq_closure_generic_point q hqa]
  exact specializes_iff_mem_closure.mp hspec

end DimensionFourDependence
