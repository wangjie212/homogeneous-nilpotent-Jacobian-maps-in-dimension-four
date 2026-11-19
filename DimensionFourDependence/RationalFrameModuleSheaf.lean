import DimensionFourDependence.RationalFrameSectionSubmodule

/-! # The actual module sheaf of locally regular rationally framed coefficients

The object is a genuine `Scheme.Modules` sheaf. Its underlying sections
are local regular functions in the specified rational frames, and the
sheaf axiom follows from the proved local predicate.
-/

namespace DimensionFourDependence

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite

universe u v

set_option synthInstance.maxHeartbeats 100000
set_option maxHeartbeats 2000000

variable (X : Scheme.{u}) [IsIntegral X] {ι : Type v}
  (frameOpen : ι → X.Opens) (weight : ι → X.functionField)

/-- The section module over each open is the module inherited from its
actual rational-value action of the structure sheaf. -/
noncomputable instance rationalFrameSectionsModule (U : X.Opens) :
    Module Γ(X, U) (rationalFrameSectionSubmodule X frameOpen weight U) := by
  let : Algebra Γ(X, U) (U → X.functionField) := schemeRationalFunctionAlgebra X U
  exact inferInstanceAs (Module Γ(X, U) (rationalFrameSectionSubmodule X frameOpen weight U))

/-- Actual restriction of locally regular coefficients as an additive
map between the original open-section modules. -/
noncomputable def rationalFrameSectionRestrict {U V : X.Opens} (j : U ⟶ V) :
    (rationalFrameSectionSubmodule X frameOpen weight V) →+
      (rationalFrameSectionSubmodule X frameOpen weight U) where
  toFun f := ⟨fun p => f.1 (j p), rationalFrameRegular_res X frameOpen weight j f.1 f.2⟩
  map_zero' := rfl
  map_add' _ _ := rfl

/-- The actual abelian presheaf underlying the rationally framed module
sheaf, with restriction of its original rational-value functions. -/
noncomputable def rationalFrameAbPresheaf : TopCat.Presheaf Ab X where
  obj U := AddCommGrpCat.of (rationalFrameSectionSubmodule X frameOpen weight U.unop)
  map j := AddCommGrpCat.ofHom (rationalFrameSectionRestrict X frameOpen weight j.unop)
  map_id U := by ext f p; rfl
  map_comp j k := by ext f p; rfl

/-- Restrictions are semilinear for the actual structure-sheaf action. -/
theorem rationalFrameSectionRestrict_smul {U V : X.Opens} (j : U ⟶ V)
    (r : Γ(X, V)) (f : rationalFrameSectionSubmodule X frameOpen weight V) :
    rationalFrameSectionRestrict X frameOpen weight j (r • f) =
      X.presheaf.map j.op r • rationalFrameSectionRestrict X frameOpen weight j f := by
  apply Subtype.ext
  funext p
  change schemeRationalSectionFunction X V r (j p) * f.1 (j p) =
    schemeRationalSectionFunction X U (X.presheaf.map j.op r) p * f.1 (j p)
  rw [schemeRationalSectionFunction_res]

/-- The genuine presheaf of modules over the scheme's actual structure
sheaf, constructed from the locally regular rational coefficients. -/
noncomputable def rationalFramePresheafOfModules : X.PresheafOfModules := by
  let M := rationalFrameAbPresheaf X frameOpen weight
  let : ∀ U : (Opens X)ᵒᵖ, Module (X.ringCatSheaf.obj.obj U) (M.obj U) := fun U =>
    inferInstanceAs (Module Γ(X, U.unop)
      (rationalFrameSectionSubmodule X frameOpen weight U.unop))
  exact PresheafOfModules.ofPresheaf M
    (fun {U V} j r f => rationalFrameSectionRestrict_smul X frameOpen weight j.unop r f)

/-- Locally regular coefficients in specified rational frames form an
actual sheaf of modules on the original scheme. No sheaf or module
axioms are supplied as assumptions. -/
noncomputable def rationalFrameModuleSheaf : X.Modules where
  val := rationalFramePresheafOfModules X frameOpen weight
  isSheaf := by
    apply (TopCat.Presheaf.isSheaf_iff_isSheaf_comp' (forget Ab) _).mpr
    change (TopCat.subpresheafToTypes
      (rationalFrameLocalPredicate X frameOpen weight).toPrelocalPredicate).IsSheaf
    exact TopCat.subpresheafToTypes.isSheaf (rationalFrameLocalPredicate X frameOpen weight)

end DimensionFourDependence
