import DimensionFourDependence.RationalFrameLocalPredicate
import DimensionFourDependence.SchemeLocallyRegularRationalFunctions

/-! # Actual regular frame coefficients extracted from the constructed sheaf

On an open contained in a frame chart, the local representatives of a
section glue to a unique regular function in that frame. Thus chart
coefficients are derived from the sheaf section rather than assumed.
-/

namespace DimensionFourDependence

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite

universe u v

set_option synthInstance.maxHeartbeats 100000
set_option maxHeartbeats 2000000

variable (X : Scheme.{u}) [IsIntegral X] {ι : Type v}
  (frameOpen : ι → X.Opens) (weight : ι → X.functionField)

/-- A section of the rationally framed sheaf has a unique actual
regular coefficient on every open contained in a nonzero frame. -/
theorem existsUnique_rational_frame_regular_coefficient
    {U : X.Opens} (i : ι) (hU : U ≤ frameOpen i) (hi : weight i ≠ 0)
    (f : U → X.functionField) (hf : RationalFrameRegular X frameOpen weight f) :
    ∃! r : Γ(X, U), f = fun p => weight i * schemeRationalSectionFunction X U r p := by
  classical
  have hlocal : ∀ p : U, ∃ (V : X.Opens) (_ : p.1 ∈ V) (hVU : V ≤ U)
      (r : Γ(X, V)), ∀ q : V,
        (f ⟨q.1, hVU q.2⟩ / weight i) = schemeRationalSectionFunction X V r q := by
    intro p
    obtain ⟨V, hpV, hVU, _, r, hr⟩ := hf p i (hU p.2)
    refine ⟨V, hpV, hVU, r, ?_⟩
    intro q
    rw [hr q]
    field_simp
  obtain ⟨r, hr, _⟩ := existsUnique_regular_section_of_local_rational_values X U
    (fun p => f p / weight i) hlocal
  have hvalue : f = fun p => weight i * schemeRationalSectionFunction X U r p := by
    funext p
    rw [congrFun hr p]
    field_simp
  refine ⟨r, hvalue, ?_⟩
  intro s hs
  apply schemeRationalSectionFunction_injective_all X U
  funext p
  apply mul_left_cancel₀ hi
  exact (congrFun hs p).symm.trans (congrFun hvalue p)

end DimensionFourDependence
