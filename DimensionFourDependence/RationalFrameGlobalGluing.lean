import DimensionFourDependence.RationalFrameGlobalSections

/-! # Actual global module-sheaf sections give regular overlap gluing coefficients -/

namespace DimensionFourDependence

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite

universe u v

set_option synthInstance.maxHeartbeats 100000
set_option maxHeartbeats 2000000

variable (X : Scheme.{u}) [IsIntegral X] {ι : Type v}
  (frameOpen : ι → X.Opens) (weight : ι → X.functionField)

/-- Common rational values of actual global sections form an additive
map, with the original pointwise values retained. -/
noncomputable def rationalFrameGlobalSectionValueAddHom :
    Γ(rationalFrameModuleSheaf X frameOpen weight, ⊤) →+ X.functionField where
  toFun := rationalFrameGlobalSectionValue X frameOpen weight
  map_zero' := rfl
  map_add' _ _ := rfl

variable (hcover : iSup frameOpen = ⊤) (hweight : ∀ i, weight i ≠ 0)

/-- The actual regular coefficient of a global module-sheaf section
on each original frame chart, constructed by regular-section gluing. -/
noncomputable def rationalFrameGlobalCoefficient
    (s : Γ(rationalFrameModuleSheaf X frameOpen weight, ⊤)) (i : ι) : Γ(X, frameOpen i) :=
  (rationalFrameGlobalSection_existsUnique_coefficient X frameOpen weight hcover s i (hweight i)).choose

/-- The actual global coefficient retains the common rational numerator. -/
theorem rationalFrameGlobalCoefficient_value
    (s : Γ(rationalFrameModuleSheaf X frameOpen weight, ⊤)) (i : ι) (p : frameOpen i) :
    rationalFrameGlobalSectionValue X frameOpen weight s =
      weight i * schemeRationalSectionFunction X (frameOpen i)
        (rationalFrameGlobalCoefficient X frameOpen weight hcover hweight s i) p :=
  (rationalFrameGlobalSection_existsUnique_coefficient X frameOpen weight hcover s i
    (hweight i)).choose_spec.1 p

/-- A nonzero actual global section has nonzero regular coefficients
on all nonempty original frame charts. -/
theorem rationalFrameGlobalCoefficient_ne_zero
    (s : Γ(rationalFrameModuleSheaf X frameOpen weight, ⊤)) (hs : s ≠ 0)
    (i : ι) [hUi : Nonempty (frameOpen i)] :
    rationalFrameGlobalCoefficient X frameOpen weight hcover hweight s i ≠ 0 := by
  intro hzero
  have hv : rationalFrameGlobalSectionValue X frameOpen weight s ≠ 0 := by
    intro h
    apply hs
    apply rationalFrameGlobalSectionValue_injective X frameOpen weight hcover
    exact h.trans (rationalFrameGlobalSectionValueAddHom X frameOpen weight).map_zero.symm
  apply hv
  have h := rationalFrameGlobalCoefficient_value X frameOpen weight hcover hweight s i (Classical.choice hUi)
  simpa only [hzero, map_zero, Pi.zero_apply, mul_zero] using h

/-- The regular coefficients extracted from an actual global section
obey the actual regular-function overlap equation in every frame change
having its specified original rational transition value. -/
theorem rationalFrameGlobalCoefficient_overlap
    (s : Γ(rationalFrameModuleSheaf X frameOpen weight, ⊤)) (i j : ι)
    (t : Γ(X, frameOpen i ⊓ frameOpen j))
    (ht : ∀ p : (frameOpen i ⊓ frameOpen j : X.Opens),
      schemeRationalSectionFunction X (frameOpen i ⊓ frameOpen j) t p = weight j / weight i) :
    X.presheaf.map (Opens.infLELeft (frameOpen i) (frameOpen j)).op
        (rationalFrameGlobalCoefficient X frameOpen weight hcover hweight s i) =
      t * X.presheaf.map (Opens.infLERight (frameOpen i) (frameOpen j)).op
        (rationalFrameGlobalCoefficient X frameOpen weight hcover hweight s j) := by
  apply schemeRationalSectionFunction_injective_all X (frameOpen i ⊓ frameOpen j)
  funext p
  simp only [map_mul, Pi.mul_apply, schemeRationalSectionFunction_res]
  rw [ht p]
  let a := schemeRationalSectionFunction X (frameOpen i)
    (rationalFrameGlobalCoefficient X frameOpen weight hcover hweight s i) ⟨p.1, p.2.1⟩
  let b := schemeRationalSectionFunction X (frameOpen j)
    (rationalFrameGlobalCoefficient X frameOpen weight hcover hweight s j) ⟨p.1, p.2.2⟩
  change a = weight j / weight i * b
  have h : weight i * a = weight j * b :=
    (rationalFrameGlobalCoefficient_value X frameOpen weight hcover hweight s i ⟨p.1, p.2.1⟩).symm.trans
      (rationalFrameGlobalCoefficient_value X frameOpen weight hcover hweight s j ⟨p.1, p.2.2⟩)
  apply mul_left_cancel₀ (hweight i)
  rw [h]
  field_simp [hweight i]

end DimensionFourDependence
