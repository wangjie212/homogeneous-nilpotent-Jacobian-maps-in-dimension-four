import DimensionFourDependence.ProjectiveCoordinateRatioSections
import DimensionFourDependence.SchemeRationalSectionFunctions

/-! # Pulled original projective ratios in an integral scheme's own function field -/

namespace DimensionFourDependence

open MvPolynomial HomogeneousLocalization AlgebraicGeometry CategoryTheory
open TopologicalSpace Opposite

attribute [local instance] MvPolynomial.gradedAlgebra

universe u

set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {C : Type u} [Field C] (Y : Scheme.{u}) [IsIntegral Y]
  (f : Y ⟶ AlgebraicGeometry.Proj (homogeneousSubmodule (Fin 4) C))

local notation "𝒢" => homogeneousSubmodule (Fin 4) C
local notation "U" a:max => Proj.basicOpen 𝒢 (X a)

/-- Every nonempty inverse coordinate chart contains the source
scheme's generic point. -/
theorem projectivePullbackGenericPoint_mem
    (hU : ∀ a : Fin 4, Nonempty (f ⁻¹ᵁ U a)) (a : Fin 4) :
    f (genericPoint Y) ∈ U a :=
  ((genericPoint_spec Y).mem_open_set_iff (f ⁻¹ᵁ U a).isOpen).mpr
    (by simpa using hU a)

/-- The actual generic stalk map evaluates homogeneous fractions at
the image of the source scheme's generic point. -/
noncomputable def projectivePullbackGenericRatioHom :
    HomogeneousLocalization 𝒢
      (f (genericPoint Y)).asHomogeneousIdeal.toIdeal.primeCompl →+* Y.functionField :=
  (f.stalkMap (genericPoint Y)).hom.comp
    (Proj.stalkIso' 𝒢 (f (genericPoint Y))).symm.toRingHom

/-- The original ratio Xi/Xa is the generic germ of its actual
regular pullback on the inverse original coordinate chart. -/
noncomputable def projectivePullbackRationalCoordinate
    (hU : ∀ a : Fin 4, Nonempty (f ⁻¹ᵁ U a)) (a i : Fin 4) : Y.functionField :=
  let : Nonempty (f ⁻¹ᵁ U a) := hU a
  Y.germToFunctionField (f ⁻¹ᵁ U a) (f.app (U a) (projectiveCoordinateRatioSection C a i))

variable (hU : ∀ a : Fin 4, Nonempty (f ⁻¹ᵁ
  Proj.basicOpen (homogeneousSubmodule (Fin 4) C) (MvPolynomial.X a)))

include hU


/-- The original rational coordinate is the image of the actual
pullback section's local germ at every point of its inverse chart. -/
theorem projectivePullbackRationalCoordinate_section_at_point (a i : Fin 4)
    (p : f ⁻¹ᵁ U a) :
    schemeRationalSectionFunction Y (f ⁻¹ᵁ U a)
        (f.app (U a) (projectiveCoordinateRatioSection C a i)) p =
      projectivePullbackRationalCoordinate Y f hU a i := by
  let : Nonempty (f ⁻¹ᵁ U a) := hU a
  exact schemeRationalSectionFunction_eq_generic Y (f ⁻¹ᵁ U a) _ p

/-- The actual generic germ equals the original homogeneous fraction
under the actual generic stalk map. -/
theorem projectivePullbackRationalCoordinate_eq_localization (a i : Fin 4) :
    projectivePullbackRationalCoordinate Y f hU a i =
      projectivePullbackGenericRatioHom Y f
        (projectiveCoordinateRatioAt C (f (genericPoint Y)) a i
          (projectivePullbackGenericPoint_mem Y f hU a)) := by
  let ha := projectivePullbackGenericPoint_mem Y f hU a
  have hstalk : (Proj.stalkIso' 𝒢 (f (genericPoint Y))).symm
      (projectiveCoordinateRatioAt C (f (genericPoint Y)) a i ha) =
      (AlgebraicGeometry.Proj 𝒢).presheaf.germ (U a) (f (genericPoint Y)) ha
        (projectiveCoordinateRatioSection C a i) := by
    apply (Proj.stalkIso' 𝒢 (f (genericPoint Y))).injective
    rw [RingEquiv.apply_symm_apply]
    exact (Proj.stalkIso'_germ 𝒢 (U a) (f (genericPoint Y)) ha
      (projectiveCoordinateRatioSection C a i)).symm
  exact (Scheme.Hom.germ_stalkMap_apply f (U a) (genericPoint Y) ha
    (projectiveCoordinateRatioSection C a i)).symm.trans
      (congrArg (fun z => f.stalkMap (genericPoint Y) z) hstalk.symm)

/-- The selected coordinate's rational ratio is exactly one. -/
theorem projectivePullbackRationalCoordinate_self (a : Fin 4) :
    projectivePullbackRationalCoordinate Y f hU a a = 1 := by
  rw [projectivePullbackRationalCoordinate_eq_localization Y f hU,
    projectiveCoordinateRatioAt_self, map_one]

/-- The original cross-chart ratio identity holds in the source
scheme's own function field. -/
theorem projectivePullbackRationalCoordinate_mul (a b i : Fin 4) :
    projectivePullbackRationalCoordinate Y f hU a i *
        projectivePullbackRationalCoordinate Y f hU b a =
      projectivePullbackRationalCoordinate Y f hU b i := by
  simp only [projectivePullbackRationalCoordinate_eq_localization Y f hU]
  rw [← map_mul, projectiveCoordinateRatioAt_mul]

/-- None of the original rational frame coordinates vanishes when
each original inverse coordinate chart is nonempty. -/
theorem projectivePullbackRationalCoordinate_ne_zero (a i : Fin 4) :
    projectivePullbackRationalCoordinate Y f hU a i ≠ 0 := by
  intro hzero
  have h := projectivePullbackRationalCoordinate_mul Y f hU a i i
  rw [hzero, zero_mul, projectivePullbackRationalCoordinate_self Y f hU] at h
  exact zero_ne_one h

/-- Every original chart ratio is the quotient of its two frame
weights, all inside the actual source scheme's function field. -/
theorem projectivePullbackRationalCoordinate_div (a b i : Fin 4) :
    projectivePullbackRationalCoordinate Y f hU a i =
      projectivePullbackRationalCoordinate Y f hU b i /
        projectivePullbackRationalCoordinate Y f hU b a :=
  (eq_div_iff (projectivePullbackRationalCoordinate_ne_zero Y f hU b a)).mpr
    (projectivePullbackRationalCoordinate_mul Y f hU a b i)

end DimensionFourDependence
