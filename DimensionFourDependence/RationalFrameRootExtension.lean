import DimensionFourDependence.NormalSchemeRationalRoots
import DimensionFourDependence.RationalFramePowers

/-! # Actual global rational-section roots extend uniquely on normal schemes -/

namespace DimensionFourDependence

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite

universe u v

set_option maxHeartbeats 1000000

variable (X : Scheme.{u}) [IsIntegral X] {ι : Type v}
  (frameOpen : ι → X.Opens) (weight : ι → X.functionField)

/-- A regular rational numerator gives an actual global section of
the original framed module sheaf, retaining that numerator. -/
noncomputable def rationalFrameGlobalSectionOfRegular (r : X.functionField)
    (hr : RationalFrameRegular X frameOpen weight (fun _ : (⊤ : X.Opens) => r)) :
    Γ(rationalFrameModuleSheaf X frameOpen weight, ⊤) :=
  (rationalFrameSheafSectionsLinearEquiv X frameOpen weight ⊤).symm ⟨(fun _ => r), hr⟩

/-- The constructed actual section has exactly the specified
original rational numerator. -/
theorem rationalFrameGlobalSectionOfRegular_value (r : X.functionField)
    (hr : RationalFrameRegular X frameOpen weight (fun _ : (⊤ : X.Opens) => r)) :
    rationalFrameGlobalSectionValue X frameOpen weight
      (rationalFrameGlobalSectionOfRegular X frameOpen weight r hr) = r := rfl

/-- An actual global section of the powered frame sheaf supplies
regularity of its common powered rational numerator in all powered frames. -/
theorem rationalFrameRegular_power_of_actual_global_section
    (hcover : iSup frameOpen = ⊤) (r : X.functionField) (d : ℕ)
    (s : Γ(rationalFramePowerModuleSheaf X frameOpen weight d, ⊤))
    (hs : rationalFrameGlobalSectionValue X frameOpen (fun i => weight i ^ d) s = r ^ d) :
    RationalFrameRegular X frameOpen (fun i => weight i ^ d)
      (fun _ : (⊤ : X.Opens) => r ^ d) := by
  let f := rationalFrameSheafSectionsLinearEquiv X frameOpen (fun i => weight i ^ d) ⊤ s
  have hf : f.1 = (fun _ : (⊤ : X.Opens) => r ^ d) := by
    funext p
    exact (rationalFrameGlobalSectionValue_at_point X frameOpen (fun i => weight i ^ d)
      hcover s p.1).trans hs
  exact hf ▸ f.2

/-- On a normal integral scheme, a rational section whose positive
power is an actual regular global section extends uniquely to an actual
global section in the original regular frames. -/
theorem existsUnique_rationalFrameGlobalSection_of_positive_power
    (hnormal : ∀ p : X, IsIntegrallyClosed (X.presheaf.stalk p))
    (hcover : iSup frameOpen = ⊤) (hweight : ∀ i, weight i ≠ 0)
    (r : X.functionField) {d : ℕ} (hd : 0 < d)
    (s : Γ(rationalFramePowerModuleSheaf X frameOpen weight d, ⊤))
    (hs : rationalFrameGlobalSectionValue X frameOpen (fun i => weight i ^ d) s = r ^ d) :
    ∃! t : Γ(rationalFrameModuleSheaf X frameOpen weight, ⊤),
      rationalFrameGlobalSectionValue X frameOpen weight t = r := by
  have hreg := rationalFrameRegular_of_positive_power X hnormal frameOpen weight hweight r hd
    (rationalFrameRegular_power_of_actual_global_section X frameOpen weight hcover r d s hs)
  refine ⟨rationalFrameGlobalSectionOfRegular X frameOpen weight r hreg, rfl, ?_⟩
  intro t ht
  apply rationalFrameGlobalSectionValue_injective X frameOpen weight hcover
  exact ht

/-- The unique regular extension of the supplied original rational
root, constructed as a genuine global module-sheaf section. -/
noncomputable def rationalFrameGlobalRootSection
    (hnormal : ∀ p : X, IsIntegrallyClosed (X.presheaf.stalk p))
    (hcover : iSup frameOpen = ⊤) (hweight : ∀ i, weight i ≠ 0)
    (r : X.functionField) {d : ℕ} (hd : 0 < d)
    (s : Γ(rationalFramePowerModuleSheaf X frameOpen weight d, ⊤))
    (hs : rationalFrameGlobalSectionValue X frameOpen (fun i => weight i ^ d) s = r ^ d) :
    Γ(rationalFrameModuleSheaf X frameOpen weight, ⊤) :=
  (existsUnique_rationalFrameGlobalSection_of_positive_power X frameOpen weight
    hnormal hcover hweight r hd s hs).choose

/-- The actual extended root retains its specified original rational
value in the scheme function field. -/
theorem rationalFrameGlobalRootSection_value
    (hnormal : ∀ p : X, IsIntegrallyClosed (X.presheaf.stalk p))
    (hcover : iSup frameOpen = ⊤) (hweight : ∀ i, weight i ≠ 0)
    (r : X.functionField) {d : ℕ} (hd : 0 < d)
    (s : Γ(rationalFramePowerModuleSheaf X frameOpen weight d, ⊤))
    (hs : rationalFrameGlobalSectionValue X frameOpen (fun i => weight i ^ d) s = r ^ d) :
    rationalFrameGlobalSectionValue X frameOpen weight
      (rationalFrameGlobalRootSection X frameOpen weight hnormal hcover hweight r hd s hs) = r :=
  (existsUnique_rationalFrameGlobalSection_of_positive_power X frameOpen weight
    hnormal hcover hweight r hd s hs).choose_spec.1

/-- The actual power of the extended actual root section equals
the originally supplied regular global powered section. -/
theorem rationalFrameGlobalRootSection_power
    (hnormal : ∀ p : X, IsIntegrallyClosed (X.presheaf.stalk p))
    (hcover : iSup frameOpen = ⊤) (hweight : ∀ i, weight i ≠ 0)
    (r : X.functionField) {d : ℕ} (hd : 0 < d)
    (s : Γ(rationalFramePowerModuleSheaf X frameOpen weight d, ⊤))
    (hs : rationalFrameGlobalSectionValue X frameOpen (fun i => weight i ^ d) s = r ^ d) :
    rationalFrameSectionPower X frameOpen weight
      (rationalFrameGlobalRootSection X frameOpen weight hnormal hcover hweight r hd s hs) d = s := by
  apply rationalFrameGlobalSectionValue_injective X frameOpen (fun i => weight i ^ d) hcover
  rw [rationalFrameSectionPower_global_value, rationalFrameGlobalRootSection_value, hs]

end DimensionFourDependence
