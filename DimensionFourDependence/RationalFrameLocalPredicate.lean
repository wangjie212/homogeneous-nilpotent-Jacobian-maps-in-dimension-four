import DimensionFourDependence.SchemeRationalSectionFunctions

/-! # The local regularity predicate for a rationally framed sheaf

On each frame open, a coefficient must locally be the specified rational
frame times an actual regular scheme function. This is an actual local
predicate on functions and therefore glues uniquely as a sheaf.
-/

namespace DimensionFourDependence

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite

universe u v

variable (X : Scheme.{u}) [IsIntegral X] {ι : Type v}
  (frameOpen : ι → X.Opens) (weight : ι → X.functionField)

/-- A rational-valued coefficient is regular in every applicable local
frame, with witnesses that are actual regular functions on neighborhoods. -/
def RationalFrameRegular {U : X.Opens} (f : U → X.functionField) : Prop :=
  ∀ (p : U) (i : ι), p.1 ∈ frameOpen i →
    ∃ (V : X.Opens) (_ : p.1 ∈ V) (hVU : V ≤ U) (_ : V ≤ frameOpen i)
      (r : Γ(X, V)), ∀ q : V,
        f ⟨q.1, hVU q.2⟩ = weight i * schemeRationalSectionFunction X V r q

/-- Restricting a locally regular framed coefficient retains its
actual local regular-function witnesses. -/
theorem rationalFrameRegular_res
    {U V : X.Opens} (j : U ⟶ V) (f : V → X.functionField)
    (hf : RationalFrameRegular X frameOpen weight f) :
    RationalFrameRegular X frameOpen weight (fun p : U => f (j p)) := by
  intro p i hp
  obtain ⟨W, hpW, hWV, hWi, r, hr⟩ := hf (j p) i hp
  refine ⟨U ⊓ W, ⟨p.2, hpW⟩, inf_le_left, inf_le_right.trans hWi,
    X.presheaf.map (homOfLE (show U ⊓ W ≤ W from inf_le_right)).op r, ?_⟩
  intro q
  rw [schemeRationalSectionFunction_res]
  exact hr ⟨q.1, q.2.2⟩

/-- Local regularity in the rational frames is a genuine sheaf-local
predicate, with no supplied sheaf axiom or gluing assumption. -/
noncomputable def rationalFrameLocalPredicate :
    TopCat.LocalPredicate (fun _ : X => X.functionField) where
  pred := RationalFrameRegular X frameOpen weight
  res := rationalFrameRegular_res X frameOpen weight
  locality := by
    intro U f hf p i hp
    obtain ⟨V, hpV, j, hV⟩ := hf p
    obtain ⟨W, hpW, hWV, hWi, r, hr⟩ := hV ⟨p.1, hpV⟩ i hp
    exact ⟨W, hpW, hWV.trans j.le, hWi, r, hr⟩

/-- The underlying sheaf of locally regular rationally framed
coefficients, constructed by the local-predicate sheaf theorem. -/
noncomputable def rationalFrameTypeSheaf : TopCat.Sheaf (Type u) X :=
  TopCat.subsheafToTypes (rationalFrameLocalPredicate X frameOpen weight)

end DimensionFourDependence
