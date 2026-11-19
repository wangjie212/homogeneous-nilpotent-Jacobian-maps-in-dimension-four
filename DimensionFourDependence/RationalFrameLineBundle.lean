import DimensionFourDependence.RationalFrameLocalTrivialization

/-! # The constructed rational frame sheaf is locally free of rank one

The local freeness property is stated for an actual scheme module
sheaf, using regular-coefficient linear equivalences on all subopens
that commute with restriction. A covering rational frame atlas supplies
this property by the verified local trivializations.
-/

namespace DimensionFourDependence

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite

universe u v

set_option synthInstance.maxHeartbeats 100000
set_option maxHeartbeats 2000000

variable {X : Scheme.{u}}

/-- An actual module sheaf has a regular rank-one frame on an open if
its sections on every subopen are naturally the structure-sheaf ring. -/
def SchemeModuleRegularFrame (M : X.Modules) (U : X.Opens) : Prop :=
  ∃ e : ∀ (V : X.Opens), V ≤ U → Γ(X, V) ≃ₗ[Γ(X, V)] Γ(M, V),
    ∀ (V W : X.Opens) (j : V ⟶ W) (hW : W ≤ U) (r : Γ(X, W)),
      M.presheaf.map j.op (e W hW r) = e V (j.le.trans hW) (X.presheaf.map j.op r)

/-- The module sheaf is locally free of rank one if every point has
a neighborhood with an actual regular frame natural on all subopens. -/
def SchemeModuleIsLocallyFreeRankOne (M : X.Modules) : Prop :=
  ∀ p : X, ∃ U : X.Opens, p ∈ U ∧ SchemeModuleRegularFrame M U

variable (X) [IsIntegral X] {ι : Type v}
  (frameOpen : ι → X.Opens) (weight : ι → X.functionField)

/-- Sections of the actual constructed module sheaf are precisely its
proved original modules of locally regular rational coefficients. -/
noncomputable def rationalFrameSheafSectionsLinearEquiv (U : X.Opens) :
    Γ(rationalFrameModuleSheaf X frameOpen weight, U) ≃ₗ[Γ(X, U)]
      rationalFrameSectionSubmodule X frameOpen weight U :=
  LinearEquiv.refl Γ(X, U) _

variable (hweight : ∀ i, weight i ≠ 0)
  (transition : ∀ i j, Γ(X, frameOpen i ⊓ frameOpen j))
  (htransition : ∀ i j (p : (frameOpen i ⊓ frameOpen j : X.Opens)),
    schemeRationalSectionFunction X (frameOpen i ⊓ frameOpen j) (transition i j) p =
      weight i / weight j)

/-- A genuine regular frame trivialization of the actual module sheaf,
with target its actual scheme-module section space. -/
noncomputable def rationalFrameSheafLocalLinearEquiv
    {U : X.Opens} (i : ι) (hU : U ≤ frameOpen i) :
    Γ(X, U) ≃ₗ[Γ(X, U)] Γ(rationalFrameModuleSheaf X frameOpen weight, U) :=
  (rationalFrameLocalLinearEquiv X frameOpen weight hweight transition htransition i hU).trans
    (rationalFrameSheafSectionsLinearEquiv X frameOpen weight U).symm

/-- The actual module-sheaf frame maps commute with all restrictions. -/
theorem rationalFrameSheafLocalLinearEquiv_restrict
    {U V : X.Opens} (j : U ⟶ V) (i : ι) (hV : V ≤ frameOpen i) (r : Γ(X, V)) :
    (rationalFrameModuleSheaf X frameOpen weight).presheaf.map j.op
      (rationalFrameSheafLocalLinearEquiv X frameOpen weight hweight transition htransition i hV r) =
      rationalFrameSheafLocalLinearEquiv X frameOpen weight hweight transition htransition i
        (j.le.trans hV) (X.presheaf.map j.op r) := by
  exact rationalFrameCoefficientLinearMap_restrict X frameOpen weight hweight transition htransition j i hV r

include hweight transition htransition in
/-- A covering rational frame atlas with actual regular transition
functions constructs a genuine locally free rank-one module sheaf. -/
theorem rationalFrameModuleSheaf_locallyFreeRankOne
    (hcover : iSup frameOpen = ⊤) :
    SchemeModuleIsLocallyFreeRankOne (rationalFrameModuleSheaf X frameOpen weight) := by
  intro p
  have hp : p ∈ iSup frameOpen := by rw [hcover]; trivial
  obtain ⟨i, hpi⟩ := Opens.mem_iSup.mp hp
  refine ⟨frameOpen i, hpi, ?_⟩
  refine ⟨fun V hV => rationalFrameSheafLocalLinearEquiv X frameOpen weight hweight transition htransition i hV, ?_⟩
  intro V W j hW r
  exact rationalFrameSheafLocalLinearEquiv_restrict X frameOpen weight hweight transition htransition j i hW r

end DimensionFourDependence
