import DimensionFourDependence.RationalFrameGlobalSections

/-! # Actual powers of sections in the original rational frames -/

namespace DimensionFourDependence

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite

universe u v

variable (X : Scheme.{u}) [IsIntegral X] {ι : Type v}
  (frameOpen : ι → X.Opens) (weight : ι → X.functionField)

/-- Taking a pointwise power of a regular framed section is regular
in the corresponding powered original frames, using actual regular powers
of the original local structure-sheaf coefficients. -/
theorem rationalFrameRegular_pow {U : X.Opens}
    (f : U → X.functionField) (hf : RationalFrameRegular X frameOpen weight f) (d : ℕ) :
    RationalFrameRegular X frameOpen (fun i => weight i ^ d) (fun p => f p ^ d) := by
  intro p i hpi
  obtain ⟨V, hpV, hVU, hVi, c, hc⟩ := hf p i hpi
  refine ⟨V, hpV, hVU, hVi, c ^ d, ?_⟩
  intro q
  change f ⟨q.1, hVU q.2⟩ ^ d = weight i ^ d * schemeRationalSectionFunction X V (c ^ d) q
  rw [hc q, mul_pow, map_pow, Pi.pow_apply]

/-- The actual original-frame power sheaf, constructed from the
same actual chart opens and powered rational frame weights. -/
noncomputable def rationalFramePowerModuleSheaf (d : ℕ) : X.Modules :=
  rationalFrameModuleSheaf X frameOpen (fun i => weight i ^ d)

/-- Taking a power produces an actual section of the actual powered
frame sheaf on the same open, not merely a rational coefficient value. -/
noncomputable def rationalFrameSectionPower {U : X.Opens}
    (s : Γ(rationalFrameModuleSheaf X frameOpen weight, U)) (d : ℕ) :
    Γ(rationalFramePowerModuleSheaf X frameOpen weight d, U) :=
  (rationalFrameSheafSectionsLinearEquiv X frameOpen (fun i => weight i ^ d) U).symm
    ⟨(fun p => (rationalFrameSheafSectionsLinearEquiv X frameOpen weight U s).1 p ^ d),
      rationalFrameRegular_pow X frameOpen weight _
        (rationalFrameSheafSectionsLinearEquiv X frameOpen weight U s).2 d⟩

/-- Actual global section powers retain the exact powered common
rational numerator in the scheme's own function field. -/
theorem rationalFrameSectionPower_global_value
    (s : Γ(rationalFrameModuleSheaf X frameOpen weight, ⊤)) (d : ℕ) :
    rationalFrameGlobalSectionValue X frameOpen (fun i => weight i ^ d)
        (rationalFrameSectionPower X frameOpen weight s d) =
      rationalFrameGlobalSectionValue X frameOpen weight s ^ d := rfl

end DimensionFourDependence
