import DimensionFourDependence.RationalFrameSectionSubmodule

/-! # Actual regular functions give sections through regular overlap transitions -/

namespace DimensionFourDependence

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite

universe u v

set_option synthInstance.maxHeartbeats 100000
set_option maxHeartbeats 2000000

variable (X : Scheme.{u}) [IsIntegral X] {ι : Type v}
  (frameOpen : ι → X.Opens) (weight : ι → X.functionField)

/-- If actual regular overlap functions have the specified rational
frame ratios, multiplying an actual regular function by a frame gives a
section regular in every overlapping frame. -/
theorem rationalFrameRegular_of_regular_coefficient
    (hweight : ∀ i, weight i ≠ 0)
    (transition : ∀ i j, Γ(X, frameOpen i ⊓ frameOpen j))
    (htransition : ∀ i j (p : (frameOpen i ⊓ frameOpen j : X.Opens)),
      schemeRationalSectionFunction X (frameOpen i ⊓ frameOpen j) (transition i j) p =
        weight i / weight j)
    {U : X.Opens} (i : ι) (hU : U ≤ frameOpen i) (r : Γ(X, U)) :
    RationalFrameRegular X frameOpen weight
      (fun p => weight i * schemeRationalSectionFunction X U r p) := by
  intro p j hpj
  let V := U ⊓ frameOpen j
  have hVij : V ≤ frameOpen i ⊓ frameOpen j :=
    fun _ h => ⟨hU h.1, h.2⟩
  refine ⟨V, ⟨p.2, hpj⟩, inf_le_left, inf_le_right,
    X.presheaf.map (homOfLE hVij).op (transition i j) *
      X.presheaf.map (homOfLE (show V ≤ U from inf_le_left)).op r, ?_⟩
  intro q
  change weight i * schemeRationalSectionFunction X U r _ = _
  simp only [map_mul, Pi.mul_apply, schemeRationalSectionFunction_res]
  rw [htransition i j]
  change weight i * schemeRationalSectionFunction X U r ⟨q.1, q.2.1⟩ =
    weight j * (weight i / weight j * schemeRationalSectionFunction X U r ⟨q.1, q.2.1⟩)
  field_simp [hweight j]

end DimensionFourDependence
