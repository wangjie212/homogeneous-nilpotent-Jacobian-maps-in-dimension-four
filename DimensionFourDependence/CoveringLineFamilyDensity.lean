import DimensionFourDependence.CoveringLineFamilySkewTriple

/-! # Every nonempty open part of a covering family still covers densely

The set of chart matrices whose line is contained in a fixed polynomial
equation is closed. Thus an equation vanishing on all lines of a nonempty
open part of an irreducible component vanishes on every member line.
The checked separation theorem then puts it in the universal incidence
kernel, which is exactly the actual image ideal for a covering component.
-/

namespace DimensionFourDependence

open MvPolynomial Matrix Topology

variable {K : Type*} [Field K]

/-- Vanishing on an actual permuted line is exactly membership in the
corresponding polynomially closed hypersurface-line chart. -/
theorem lineChartMemberLine_contained_iff_chart [Infinite K]
    (p : Equiv.Perm (Fin 4)) (B : Matrix (Fin 2) (Fin 2) K) (P : MvPolynomial (Fin 4) K) :
    (∀ x ∈ lineChartMemberLine p B, aeval x P = 0) ↔
      B ∈ hypersurfaceLineChart (rename p.symm P) := by
  constructor
  · intro h
    apply (hypersurfaceLineChart_mem_iff_line_contained _ B).mpr
    intro z hz
    rw [aeval_rename]
    exact h ((lineCoordinatePermutation p).symm z) ⟨z, hz, rfl⟩
  · intro h
    exact hypersurfaceAtlasLine_contained P ⟨p, ⟨B, h⟩⟩

variable [IsAlgClosed K]
variable (Q : Ideal (MvPolynomial (Fin 2 × Fin 2) K)) [Q.IsPrime]

omit [IsAlgClosed K] [Q.IsPrime] in
/-- A zero in the universal incidence ring vanishes on every actual
point of every member line of the component. -/
theorem componentLineIncidenceHom_zero_on_component_lines
    (p : Equiv.Perm (Fin 4)) (P : MvPolynomial (Fin 4) K)
    (hP : componentLineIncidenceHom p Q P = 0) :
    ∀ B ∈ lineComponentPoints Q, ∀ x ∈ lineChartMemberLine p B, aeval x P = 0 := by
  intro B hB x hx
  obtain ⟨z, hz, hzx⟩ := hx
  obtain ⟨u, hu⟩ := (mem_graphLineFour B z).mp hz
  have hcoords : x = fun i => (![u 0, u 1, (B *ᵥ u) 0, (B *ᵥ u) 1] : Fin 4 → K)
      (p.symm i) := by
    rw [← hzx, hu]
    rfl
  have he := componentLineIncidenceHom_evaluate p B u Q
    (lineComponentPoints_le_extendedPrime Q B hB) P
  rw [hP, map_zero, ← hcoords] at he
  exact he.symm

/-- Vanishing on every line in a nonempty open part of the actual
component forces vanishing in the entire universal incidence ring. -/
theorem componentLineIncidenceHom_eq_zero_of_open_component_lines
    (p : Equiv.Perm (Fin 4)) (P : MvPolynomial (Fin 4) K) :
    letI := graphLineChartTopology K
    ∀ (U : Set (lineComponentPoints Q)), IsOpen U → U.Nonempty →
      (∀ B ∈ U, ∀ x ∈ lineChartMemberLine p B.val, aeval x P = 0) →
      componentLineIncidenceHom p Q P = 0 := by
  let : TopologicalSpace (Matrix (Fin 2) (Fin 2) K) := graphLineChartTopology K
  let : PreirreducibleSpace (lineComponentPoints Q) :=
    Subtype.preirreducibleSpace (lineComponentPoints_isIrreducible Q).isPreirreducible
  intro U hU hUne hP
  let C : Set (lineComponentPoints Q) :=
    {B | B.val ∈ hypersurfaceLineChart (rename p.symm P)}
  have hC : IsClosed C :=
    (hypersurfaceLineChart_isClosed (rename p.symm P)).preimage continuous_subtype_val
  have hUC : U ⊆ C := fun B hB =>
    (lineChartMemberLine_contained_iff_chart p B.val P).mp (hP B hB)
  have hdense : Dense U := hU.dense hUne
  have hall : ∀ B : lineComponentPoints Q, B ∈ C := fun B =>
    (hC.closure_subset_iff.mpr hUC) (hdense B)
  apply componentLineIncidenceHom_eq_zero_of_component_lines Q p P
  intro B hB
  exact (lineChartMemberLine_contained_iff_chart p B P).mpr (hall ⟨B, hB⟩)

/-- The actual output points on lines in a specified part of a component. -/
def lineComponentSubfamilyImage (p : Equiv.Perm (Fin 4))
    (U : Set (lineComponentPoints Q)) : Set (Fin 4 → K) :=
  {x | ∃ B ∈ U, x ∈ lineChartMemberLine p B.val}

/-- Every nonempty open part of a covering component has exactly the
actual image ideal as its ideal of equations on its actual output points. -/
theorem covering_line_component_open_image_vanishingIdeal
    (H : Fin 4 → MvPolynomial (Fin 4) K) (p : Equiv.Perm (Fin 4))
    (hk : RingHom.ker (componentLineIncidenceHom p Q) = imageRelationIdeal H) :
    letI := graphLineChartTopology K
    ∀ (U : Set (lineComponentPoints Q)), IsOpen U → U.Nonempty →
      MvPolynomial.vanishingIdeal K (lineComponentSubfamilyImage Q p U) = imageRelationIdeal H := by
  let : TopologicalSpace (Matrix (Fin 2) (Fin 2) K) := graphLineChartTopology K
  intro U hU hUne
  rw [← hk]
  ext P
  constructor
  · intro hP
    apply componentLineIncidenceHom_eq_zero_of_open_component_lines Q p P U hU hUne
    intro B hB x hx
    exact hP x ⟨B, hB, hx⟩
  · intro hP x hx
    obtain ⟨B, hB, hx⟩ := hx
    exact componentLineIncidenceHom_zero_on_component_lines Q p P hP B.val B.property x hx

/-- Actual output points of every nonempty open part of a covering
line family are dense in the actual affine image cone, using the actual
point-to-prime embedding and Mathlib's spectrum closure. -/
theorem covering_line_component_open_image_spectrum_closure
    (H : Fin 4 → MvPolynomial (Fin 4) K) (p : Equiv.Perm (Fin 4))
    (hk : RingHom.ker (componentLineIncidenceHom p Q) = imageRelationIdeal H) :
    letI := graphLineChartTopology K
    ∀ (U : Set (lineComponentPoints Q)), IsOpen U → U.Nonempty →
      closure (MvPolynomial.pointToPoint (k := K) '' lineComponentSubfamilyImage Q p U) =
        PrimeSpectrum.zeroLocus (imageRelationIdeal H : Set (MvPolynomial (Fin 4) K)) := by
  let : TopologicalSpace (Matrix (Fin 2) (Fin 2) K) := graphLineChartTopology K
  intro U hU hUne
  rw [← PrimeSpectrum.zeroLocus_vanishingIdeal_eq_closure,
    MvPolynomial.vanishingIdeal_pointToPoint,
    covering_line_component_open_image_vanishingIdeal Q H p hk U hU hUne]

end DimensionFourDependence
