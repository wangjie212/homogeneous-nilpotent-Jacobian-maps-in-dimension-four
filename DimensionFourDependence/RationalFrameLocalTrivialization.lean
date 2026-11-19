import DimensionFourDependence.RationalFrameModuleSheaf
import DimensionFourDependence.RationalFrameLocalCoefficient
import DimensionFourDependence.RationalFrameRegularCoefficient

/-! # Local rank-one trivializations of the actual rational frame module sheaf

Actual regular overlap functions with the specified frame ratios give
mutually inverse regular coefficient and section maps. The resulting
linear trivializations commute with restriction to smaller opens.
-/

namespace DimensionFourDependence

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite

universe u v

set_option synthInstance.maxHeartbeats 100000
set_option maxHeartbeats 2000000

variable (X : Scheme.{u}) [IsIntegral X] {ι : Type v}
  (frameOpen : ι → X.Opens) (weight : ι → X.functionField)
  (hweight : ∀ i, weight i ≠ 0)
  (transition : ∀ i j, Γ(X, frameOpen i ⊓ frameOpen j))
  (htransition : ∀ i j (p : (frameOpen i ⊓ frameOpen j : X.Opens)),
    schemeRationalSectionFunction X (frameOpen i ⊓ frameOpen j) (transition i j) p =
      weight i / weight j)

/-- A regular function in one original frame gives a linear section
of the constructed module sheaf, regular in every overlapping frame. -/
noncomputable def rationalFrameCoefficientLinearMap
    {U : X.Opens} (i : ι) (hU : U ≤ frameOpen i) :
    Γ(X, U) →ₗ[Γ(X, U)] rationalFrameSectionSubmodule X frameOpen weight U where
  toFun r := ⟨fun p => weight i * schemeRationalSectionFunction X U r p,
    rationalFrameRegular_of_regular_coefficient X frameOpen weight hweight transition htransition i hU r⟩
  map_add' := by
    intro r s
    apply Subtype.ext
    funext p
    change weight i * schemeRationalSectionFunction X U (r + s) p =
      weight i * schemeRationalSectionFunction X U r p + weight i * schemeRationalSectionFunction X U s p
    simp only [map_add, Pi.add_apply]
    ring
  map_smul' := by
    intro r s
    apply Subtype.ext
    funext p
    change weight i * schemeRationalSectionFunction X U (r * s) p =
      schemeRationalSectionFunction X U r p * (weight i * schemeRationalSectionFunction X U s p)
    simp only [map_mul, Pi.mul_apply]
    ring

/-- Each coefficient map is bijective on an open contained in its
frame chart; its inverse is constructed by actual regular-section gluing. -/
theorem rationalFrameCoefficientLinearMap_bijective
    {U : X.Opens} (i : ι) (hU : U ≤ frameOpen i) :
    Function.Bijective (rationalFrameCoefficientLinearMap X frameOpen weight hweight transition htransition i hU) := by
  constructor
  · intro r s hrs
    apply schemeRationalSectionFunction_injective_all X U
    funext p
    apply mul_left_cancel₀ (hweight i)
    exact congrArg (fun f : rationalFrameSectionSubmodule X frameOpen weight U => f.1 p) hrs
  · intro f
    obtain ⟨r, hr, _⟩ := existsUnique_rational_frame_regular_coefficient X frameOpen weight i hU
      (hweight i) f.1 f.2
    refine ⟨r, ?_⟩
    apply Subtype.ext
    exact hr.symm

/-- Every local frame trivializes the actual section module as a free
module of rank one over the actual structure-sheaf ring on that open. -/
noncomputable def rationalFrameLocalLinearEquiv
    {U : X.Opens} (i : ι) (hU : U ≤ frameOpen i) :
    Γ(X, U) ≃ₗ[Γ(X, U)] rationalFrameSectionSubmodule X frameOpen weight U :=
  LinearEquiv.ofBijective (rationalFrameCoefficientLinearMap X frameOpen weight hweight transition htransition i hU)
    (rationalFrameCoefficientLinearMap_bijective X frameOpen weight hweight transition htransition i hU)

/-- The rank-one local trivializations commute with the actual
restriction maps of the structure sheaf and constructed module sheaf. -/
theorem rationalFrameCoefficientLinearMap_restrict
    {U V : X.Opens} (j : U ⟶ V) (i : ι) (hV : V ≤ frameOpen i) (r : Γ(X, V)) :
    rationalFrameSectionRestrict X frameOpen weight j
      (rationalFrameCoefficientLinearMap X frameOpen weight hweight transition htransition i hV r) =
      rationalFrameCoefficientLinearMap X frameOpen weight hweight transition htransition i
        (j.le.trans hV) (X.presheaf.map j.op r) := by
  apply Subtype.ext
  funext p
  change weight i * schemeRationalSectionFunction X V r (j p) =
    weight i * schemeRationalSectionFunction X U (X.presheaf.map j.op r) p
  rw [schemeRationalSectionFunction_res]

end DimensionFourDependence
