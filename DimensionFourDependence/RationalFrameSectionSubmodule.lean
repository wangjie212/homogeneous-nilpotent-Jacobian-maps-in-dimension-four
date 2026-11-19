import DimensionFourDependence.RationalFrameLocalPredicate

/-! # Locally regular rationally framed sections form actual structure-sheaf modules -/

namespace DimensionFourDependence

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite

universe u v

set_option synthInstance.maxHeartbeats 100000
set_option maxHeartbeats 2000000

variable (X : Scheme.{u}) [IsIntegral X] {ι : Type v}
  (frameOpen : ι → X.Opens) (weight : ι → X.functionField)

/-- The zero coefficient is regular in every rational frame. -/
theorem rationalFrameRegular_zero (U : X.Opens) :
    RationalFrameRegular X frameOpen weight (0 : U → X.functionField) := by
  intro p i hp
  refine ⟨U ⊓ frameOpen i, ⟨p.2, hp⟩, inf_le_left, inf_le_right, 0, ?_⟩
  intro q
  simp

/-- Local regularity is closed under addition of section coefficients. -/
theorem rationalFrameRegular_add {U : X.Opens} (f g : U → X.functionField)
    (hf : RationalFrameRegular X frameOpen weight f)
    (hg : RationalFrameRegular X frameOpen weight g) :
    RationalFrameRegular X frameOpen weight (f + g) := by
  intro p i hp
  obtain ⟨V, hpV, hVU, hVi, a, ha⟩ := hf p i hp
  obtain ⟨W, hpW, hWU, hWi, b, hb⟩ := hg p i hp
  refine ⟨V ⊓ W, ⟨hpV, hpW⟩, inf_le_left.trans hVU, inf_le_left.trans hVi,
    X.presheaf.map (homOfLE (show V ⊓ W ≤ V from inf_le_left)).op a +
      X.presheaf.map (homOfLE (show V ⊓ W ≤ W from inf_le_right)).op b, ?_⟩
  intro q
  change f _ + g _ = _
  rw [ha ⟨q.1, q.2.1⟩, hb ⟨q.1, q.2.2⟩]
  simp only [map_add, Pi.add_apply, schemeRationalSectionFunction_res]
  change weight i * schemeRationalSectionFunction X V a ⟨q.1, q.2.1⟩ +
      weight i * schemeRationalSectionFunction X W b ⟨q.1, q.2.2⟩ =
    weight i * (schemeRationalSectionFunction X V a ⟨q.1, q.2.1⟩ +
      schemeRationalSectionFunction X W b ⟨q.1, q.2.2⟩)
  ring

/-- An actual regular structure-sheaf function acts on framed sections
by its actual rational germ values and preserves local regularity. -/
theorem rationalFrameRegular_smul {U : X.Opens} (r : Γ(X, U)) (f : U → X.functionField)
    (hf : RationalFrameRegular X frameOpen weight f) :
    RationalFrameRegular X frameOpen weight
      (fun p => schemeRationalSectionFunction X U r p * f p) := by
  intro p i hp
  obtain ⟨V, hpV, hVU, hVi, a, ha⟩ := hf p i hp
  refine ⟨V, hpV, hVU, hVi, X.presheaf.map (homOfLE hVU).op r * a, ?_⟩
  intro q
  change schemeRationalSectionFunction X U r ⟨q.1, hVU q.2⟩ * f ⟨q.1, hVU q.2⟩ = _
  rw [ha q]
  simp only [map_mul, Pi.mul_apply, schemeRationalSectionFunction_res]
  change schemeRationalSectionFunction X U r ⟨q.1, hVU q.2⟩ *
      (weight i * schemeRationalSectionFunction X V a q) =
    weight i * (schemeRationalSectionFunction X U r ⟨q.1, hVU q.2⟩ *
      schemeRationalSectionFunction X V a q)
  ring

/-- On every open the locally regular rationally framed coefficients
form a genuine module over that open's actual regular functions. -/
noncomputable def rationalFrameSectionSubmodule (U : X.Opens) :
    let : Algebra Γ(X, U) (U → X.functionField) := schemeRationalFunctionAlgebra X U
    Submodule Γ(X, U) (U → X.functionField) := by
  let : Algebra Γ(X, U) (U → X.functionField) := schemeRationalFunctionAlgebra X U
  refine
    { carrier := RationalFrameRegular X frameOpen weight
      zero_mem' := rationalFrameRegular_zero X frameOpen weight U
      add_mem' := fun hf hg => rationalFrameRegular_add X frameOpen weight _ _ hf hg
      smul_mem' := ?_ }
  intro r f hf
  change RationalFrameRegular X frameOpen weight
    (fun p => schemeRationalSectionFunction X U r p * f p)
  exact rationalFrameRegular_smul X frameOpen weight r f hf

end DimensionFourDependence
