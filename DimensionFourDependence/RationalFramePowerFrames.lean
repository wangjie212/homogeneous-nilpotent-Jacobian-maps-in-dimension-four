import DimensionFourDependence.RationalFramePowers
import DimensionFourDependence.RationalFrameGlobalGluing

/-! # Powered original frames remain actual rank-one frames -/

namespace DimensionFourDependence

open AlgebraicGeometry CategoryTheory TopologicalSpace

universe u v

variable (X : Scheme.{u}) [IsIntegral X] {ι : Type v}

/-- Replacing a frame-open family by its equal actual opens retains
the same local regularity, without changing any regular representatives. -/
theorem rationalFrameRegular_of_open_eq
    (frameOpen frameOpen' : ι → X.Opens) (weight : ι → X.functionField)
    (hopen : ∀ i, frameOpen i = frameOpen' i)
    {U : X.Opens} (f : U → X.functionField)
    (hf : RationalFrameRegular X frameOpen weight f) :
    RationalFrameRegular X frameOpen' weight f :=
  (funext hopen) ▸ hf

variable (frameOpen : ι → X.Opens) (weight : ι → X.functionField)

/-- Actual regular frame transitions raise to the expected frame
ratios on every actual overlap. -/
theorem rationalFrameTransition_pow_value
    (transition : ∀ i j, Γ(X, frameOpen i ⊓ frameOpen j))
    (htransition : ∀ i j (p : (frameOpen i ⊓ frameOpen j : X.Opens)),
      schemeRationalSectionFunction X _ (transition i j) p = weight i / weight j)
    (d : ℕ) (i j : ι) (p : (frameOpen i ⊓ frameOpen j : X.Opens)) :
    schemeRationalSectionFunction X _ (transition i j ^ d) p = weight i ^ d / weight j ^ d := by
  rw [map_pow, Pi.pow_apply, htransition, div_pow]

/-- The actual powered-frame sheaf is locally free of rank one,
with actual regular powered overlap transitions on the same frame cover. -/
theorem rationalFramePowerModuleSheaf_locallyFreeRankOne
    (hcover : iSup frameOpen = ⊤) (hweight : ∀ i, weight i ≠ 0)
    (transition : ∀ i j, Γ(X, frameOpen i ⊓ frameOpen j))
    (htransition : ∀ i j (p : (frameOpen i ⊓ frameOpen j : X.Opens)),
      schemeRationalSectionFunction X _ (transition i j) p = weight i / weight j) (d : ℕ) :
    SchemeModuleIsLocallyFreeRankOne (rationalFramePowerModuleSheaf X frameOpen weight d) :=
  rationalFrameModuleSheaf_locallyFreeRankOne X frameOpen (fun i => weight i ^ d)
    (fun i => pow_ne_zero d (hweight i)) (fun i j => transition i j ^ d)
    (rationalFrameTransition_pow_value X frameOpen weight transition htransition d) hcover

/-- Taking the actual power section raises each actual regular
original-frame coefficient to the same power in its actual chart ring. -/
theorem rationalFrameGlobalCoefficient_power
    (hcover : iSup frameOpen = ⊤) (hweight : ∀ i, weight i ≠ 0)
    (s : Γ(rationalFrameModuleSheaf X frameOpen weight, ⊤)) (d : ℕ) (i : ι) :
    rationalFrameGlobalCoefficient X frameOpen (fun j => weight j ^ d) hcover
        (fun j => pow_ne_zero d (hweight j)) (rationalFrameSectionPower X frameOpen weight s d) i =
      rationalFrameGlobalCoefficient X frameOpen weight hcover hweight s i ^ d := by
  apply schemeRationalSectionFunction_injective_all X (frameOpen i)
  funext p
  simp only [map_pow, Pi.pow_apply]
  apply mul_left_cancel₀ (pow_ne_zero d (hweight i))
  calc
    _ = rationalFrameGlobalSectionValue X frameOpen (fun j => weight j ^ d)
        (rationalFrameSectionPower X frameOpen weight s d) :=
      (rationalFrameGlobalCoefficient_value X frameOpen (fun j => weight j ^ d) hcover
        (fun j => pow_ne_zero d (hweight j)) _ i p).symm
    _ = rationalFrameGlobalSectionValue X frameOpen weight s ^ d :=
      rationalFrameSectionPower_global_value X frameOpen weight s d
    _ = (weight i * schemeRationalSectionFunction X (frameOpen i)
        (rationalFrameGlobalCoefficient X frameOpen weight hcover hweight s i) p) ^ d :=
      congrArg (fun z => z ^ d)
        (rationalFrameGlobalCoefficient_value X frameOpen weight hcover hweight s i p)
    _ = _ := mul_pow _ _ d

end DimensionFourDependence
