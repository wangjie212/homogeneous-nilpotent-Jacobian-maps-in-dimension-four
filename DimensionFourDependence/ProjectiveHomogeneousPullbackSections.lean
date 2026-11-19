import DimensionFourDependence.ProjectiveHomogeneousPullbackCoefficients
import DimensionFourDependence.RationalFrameRootExtension
import DimensionFourDependence.RationalFramePowerFrames

/-! # Original homogeneous forms define actual global powered-frame sections -/

namespace DimensionFourDependence

open MvPolynomial AlgebraicGeometry CategoryTheory TopologicalSpace

attribute [local instance] MvPolynomial.gradedAlgebra

universe u

set_option maxHeartbeats 1000000
set_option quotPrecheck false

variable {C : Type u} [Field C] (Y : Scheme.{u}) [IsIntegral Y]
  (f : Y ⟶ AlgebraicGeometry.Proj (homogeneousSubmodule (Fin 4) C))

local notation "U" a:max => f ⁻¹ᵁ Proj.basicOpen (homogeneousSubmodule (Fin 4) C) (X a)

/-- An original degree-d homogeneous polynomial has an actually
regular common rational numerator in all powered original frames. -/
theorem projectiveHomogeneousPullback_regular
    (hU : ∀ a : Fin 4, Nonempty (U a))
    (P : MvPolynomial (Fin 4) C) {d : ℕ} (hP : P.IsHomogeneous d) :
    let : Algebra C Y.functionField := projectivePullbackFunctionFieldAlgebra Y f
    RationalFrameRegular Y (fun a : Fin 4 => U a)
      (fun a => projectivePullbackHyperplaneWeight Y f hU a ^ d)
      (fun _ : (⊤ : Y.Opens) => aeval (projectivePullbackHyperplaneWeight Y f hU) P) := by
  let : Algebra C Y.functionField := projectivePullbackFunctionFieldAlgebra Y f
  dsimp only
  intro p a hpa
  refine ⟨U a, hpa, le_top, le_rfl, projectivePullbackChartPolynomialHom Y f a P, ?_⟩
  intro q
  exact (projectivePullbackChartPolynomialHom_homogeneous_numerator Y f hU P hP a q).symm

/-- The actual global powered-frame section of an original
homogeneous source polynomial. -/
noncomputable def projectiveHomogeneousPullbackSection
    (hU : ∀ a : Fin 4, Nonempty (U a))
    (P : MvPolynomial (Fin 4) C) {d : ℕ} (hP : P.IsHomogeneous d) :
    Γ(rationalFramePowerModuleSheaf Y (fun a : Fin 4 => U a)
      (projectivePullbackHyperplaneWeight Y f hU) d, ⊤) := by
  let : Algebra C Y.functionField := projectivePullbackFunctionFieldAlgebra Y f
  exact rationalFrameGlobalSectionOfRegular Y (fun a : Fin 4 => U a)
    (fun a => projectivePullbackHyperplaneWeight Y f hU a ^ d)
    (aeval (projectivePullbackHyperplaneWeight Y f hU) P)
    (projectiveHomogeneousPullback_regular Y f hU P hP)

/-- The actual source-polynomial global section retains its exact
homogeneous rational numerator in the own scheme function field. -/
theorem projectiveHomogeneousPullbackSection_value
    (hU : ∀ a : Fin 4, Nonempty (U a))
    (P : MvPolynomial (Fin 4) C) {d : ℕ} (hP : P.IsHomogeneous d) :
    let : Algebra C Y.functionField := projectivePullbackFunctionFieldAlgebra Y f
    rationalFrameGlobalSectionValue Y (fun a : Fin 4 => U a)
        (fun a => projectivePullbackHyperplaneWeight Y f hU a ^ d)
        (projectiveHomogeneousPullbackSection Y f hU P hP) =
      aeval (projectivePullbackHyperplaneWeight Y f hU) P := by
  let : Algebra C Y.functionField := projectivePullbackFunctionFieldAlgebra Y f
  rfl

end DimensionFourDependence
