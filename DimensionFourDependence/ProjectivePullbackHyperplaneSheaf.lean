import DimensionFourDependence.ProjectivePullbackRationalCoordinates
import DimensionFourDependence.RationalFrameGlobalGluing

/-! # An actual rank-one module sheaf with the original projective hyperplane frames -/

namespace DimensionFourDependence

open MvPolynomial AlgebraicGeometry CategoryTheory TopologicalSpace Opposite

attribute [local instance] MvPolynomial.gradedAlgebra

universe u

set_option maxHeartbeats 1000000
set_option quotPrecheck false

variable {C : Type u} [Field C] (Y : Scheme.{u}) [IsIntegral Y]
  (f : Y ⟶ AlgebraicGeometry.Proj (homogeneousSubmodule (Fin 4) C))

local notation "𝒢" => homogeneousSubmodule (Fin 4) C
local notation "U" a:max => f ⁻¹ᵁ Proj.basicOpen 𝒢 (X a)

variable (hU : ∀ a : Fin 4, Nonempty (f ⁻¹ᵁ
  Proj.basicOpen (homogeneousSubmodule (Fin 4) C) (MvPolynomial.X a)))

/-- The original hyperplane frame Xa, expressed as Xa/X0 in the
actual source scheme's own function field. -/
noncomputable def projectivePullbackHyperplaneWeight (a : Fin 4) : Y.functionField :=
  projectivePullbackRationalCoordinate Y f hU 0 a

include hU in
/-- Each original hyperplane frame has nonzero rational weight. -/
theorem projectivePullbackHyperplaneWeight_ne_zero (a : Fin 4) :
    projectivePullbackHyperplaneWeight Y f hU a ≠ 0 :=
  projectivePullbackRationalCoordinate_ne_zero Y f hU 0 a

/-- The actual regular change from frame j to frame i is Xi/Xj,
restricted from its original regular projective chart. -/
noncomputable def projectivePullbackHyperplaneTransition (i j : Fin 4) :
    Γ(Y, U i ⊓ U j) :=
  Y.presheaf.map (Opens.infLERight (U i) (U j)).op
    (f.app (Proj.basicOpen 𝒢 (X j)) (projectiveCoordinateRatioSection C j i))

include hU in
/-- Every actual regular overlap transition has exactly the quotient
of its original frame weights as rational value. -/
theorem projectivePullbackHyperplaneTransition_value (i j : Fin 4)
    (p : (U i ⊓ U j : Y.Opens)) :
    schemeRationalSectionFunction Y (U i ⊓ U j)
        (projectivePullbackHyperplaneTransition Y f i j) p =
      projectivePullbackHyperplaneWeight Y f hU i /
        projectivePullbackHyperplaneWeight Y f hU j := by
  unfold projectivePullbackHyperplaneTransition
  rw [schemeRationalSectionFunction_res,
    projectivePullbackRationalCoordinate_section_at_point Y f hU]
  exact projectivePullbackRationalCoordinate_div Y f hU j 0 i

/-- The module sheaf of regular hyperplane-frame representatives,
constructed on the actual source scheme. -/
noncomputable def projectivePullbackHyperplaneModuleSheaf : Y.Modules :=
  rationalFrameModuleSheaf Y (fun a : Fin 4 => U a)
    (projectivePullbackHyperplaneWeight Y f hU)

include hU in
/-- The constructed actual hyperplane-frame module sheaf is locally
free of rank one whenever the original inverse coordinate opens cover. -/
theorem projectivePullbackHyperplaneModuleSheaf_locallyFreeRankOne
    (hcover : ⨆ a : Fin 4, U a = ⊤) :
    SchemeModuleIsLocallyFreeRankOne (projectivePullbackHyperplaneModuleSheaf Y f hU) := by
  exact rationalFrameModuleSheaf_locallyFreeRankOne Y (fun a : Fin 4 => U a)
    (projectivePullbackHyperplaneWeight Y f hU)
    (projectivePullbackHyperplaneWeight_ne_zero Y f hU)
    (projectivePullbackHyperplaneTransition Y f)
    (projectivePullbackHyperplaneTransition_value Y f hU) hcover

end DimensionFourDependence
