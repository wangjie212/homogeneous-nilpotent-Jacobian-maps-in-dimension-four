import DimensionFourDependence.ActivePencilPerturbationConjugacy
import DimensionFourDependence.LinearBaseShearFrame

/-! # An actual tame coordinate change of the two base variables -/

namespace DimensionFourDependence.Shear

open Matrix MvPolynomial

variable {K : Type*} [Field K]
local notation "R₂" => MvPolynomial (Fin 2) K
local notation "R₄" => MvPolynomial (Fin 4) K
local notation "Aut₄" => R₄ ≃ₐ[K] R₄
local notation "M₂" => Matrix (Fin 2) (Fin 2) K

private theorem one_det_isUnit : IsUnit (1 : M₂).det := by simp

/-- Changing the base variables acts trivially on the active variables.
The two signs in the two constituent affine frames cancel. -/
noncomputable def binaryPencilBaseFrame (T : M₂) (hT : IsUnit T.det) : Aut₄ :=
  signBaseFrameEquiv4 T hT * signBaseFrameEquiv4 1 one_det_isUnit

theorem binaryPencilBaseFrame_tame (T : M₂) (hT : IsUnit T.det) :
    binaryPencilBaseFrame T hT ∈ Tame.subgroup K 4 := by
  exact (Tame.subgroup K 4).mul_mem
    (Subgroup.subset_closure (Or.inl (signBaseFrameEquiv4_isAffine T hT)))
    (Subgroup.subset_closure (Or.inl (signBaseFrameEquiv4_isAffine 1 one_det_isUnit)))

theorem binaryPencilBaseFrame_X_zero (T : M₂) (hT : IsUnit T.det) :
    binaryPencilBaseFrame T hT (X 0) = X 0 := by
  simp [binaryPencilBaseFrame, AlgEquiv.mul_apply, signBaseFrameEquiv4_X]

theorem binaryPencilBaseFrame_X_one (T : M₂) (hT : IsUnit T.det) :
    binaryPencilBaseFrame T hT (X 1) = X 1 := by
  simp [binaryPencilBaseFrame, AlgEquiv.mul_apply, signBaseFrameEquiv4_X]

theorem binaryPencilBaseFrame_base (T : M₂) (hT : IsUnit T.det) (p : R₂) :
    binaryPencilBaseFrame T hT (base4 p) = base4 (linearPolynomialPullback T p) := by
  have h : aeval (linearPolynomialMap (1 : M₂)) = AlgHom.id K R₂ := by
    apply MvPolynomial.algHom_ext
    intro i
    simp [linearPolynomialMap, Matrix.one_apply, eq_comm]
  have hi : linearPolynomialPullback (1 : M₂) p = p := AlgHom.congr_fun h p
  simp only [binaryPencilBaseFrame, AlgEquiv.mul_apply, signBaseFrameEquiv4_base, hi]

end DimensionFourDependence.Shear
