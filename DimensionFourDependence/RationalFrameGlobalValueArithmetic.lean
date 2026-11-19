import DimensionFourDependence.RationalFrameGlobalGluing

/-! # Actual global framed-section sums and regular scalar multiplication retain their values -/

namespace DimensionFourDependence

open AlgebraicGeometry CategoryTheory TopologicalSpace

universe u v

variable (X : Scheme.{u}) [IsIntegral X] {ι : Type v}
  (frameOpen : ι → X.Opens) (weight : ι → X.functionField)

local instance rationalFrameGlobalValueArithmeticTopNonempty : Nonempty (⊤ : X.Opens) :=
  ⟨⟨genericPoint X, trivial⟩⟩

/-- Actual addition of global framed sections adds their actual
common rational numerators. -/
theorem rationalFrameGlobalSectionValue_add
    (s t : Γ(rationalFrameModuleSheaf X frameOpen weight, ⊤)) :
    rationalFrameGlobalSectionValue X frameOpen weight (s + t) =
      rationalFrameGlobalSectionValue X frameOpen weight s +
        rationalFrameGlobalSectionValue X frameOpen weight t := rfl

/-- Actual regular global functions multiply actual framed sections
with exactly their original rational-function values. -/
theorem rationalFrameGlobalSectionValue_smul
    (a : Γ(X, ⊤)) (s : Γ(rationalFrameModuleSheaf X frameOpen weight, ⊤)) :
    rationalFrameGlobalSectionValue X frameOpen weight (a • s) =
      X.germToFunctionField ⊤ a * rationalFrameGlobalSectionValue X frameOpen weight s := by
  change schemeRationalSectionFunction X ⊤ a ⟨genericPoint X, trivial⟩ *
    rationalFrameGlobalSectionValue X frameOpen weight s = _
  rw [schemeRationalSectionFunction_eq_generic]

/-- Each actual global section coefficient is its common rational
numerator divided by the nonzero original frame weight. -/
theorem rationalFrameGlobalCoefficient_generic_value
    (hcover : iSup frameOpen = ⊤) (hweight : ∀ i, weight i ≠ 0)
    (s : Γ(rationalFrameModuleSheaf X frameOpen weight, ⊤))
    (i : ι) [hU : Nonempty (frameOpen i)] :
    X.germToFunctionField (frameOpen i)
        (rationalFrameGlobalCoefficient X frameOpen weight hcover hweight s i) =
      rationalFrameGlobalSectionValue X frameOpen weight s / weight i := by
  apply (eq_div_iff (hweight i)).mpr
  have h := rationalFrameGlobalCoefficient_value X frameOpen weight hcover hweight s i (Classical.choice hU)
  rw [schemeRationalSectionFunction_eq_generic] at h
  exact (mul_comm _ _).trans h.symm

end DimensionFourDependence
