import DimensionFourDependence.LinearConjugacyRank
import DimensionFourDependence.ImageEquationWitness
import DimensionFourDependence.GaussNormalChart
import Mathlib.Algebra.Group.Irreducible.Lemmas

/-! # Actual image equations and normals under source-target conjugacy -/

namespace DimensionFourDependence

open MvPolynomial Matrix

set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 100000

variable {K : Type*} [Field K] {n : ℕ}

/-- Substituting the transformed image equation in the conjugated map
is precisely the original vanishing equation in the new source coordinates. -/
theorem aeval_linearPolynomialPullback_conjugate
    (T S : Matrix (Fin n) (Fin n) K) (hTS : T * S = 1)
    (H : Fin n → MvPolynomial (Fin n) K) (F : MvPolynomial (Fin n) K) :
    aeval (linearPolynomialConjugate T S H) (linearPolynomialPullback T F) =
      linearPolynomialPullback T (aeval H F) := by
  have hTSC : T.map (MvPolynomial.C : K →+* MvPolynomial (Fin n) K) * S.map MvPolynomial.C = 1 := by
    rw [← Matrix.map_mul, hTS]
    ext i j
    simp [Matrix.one_apply]
  have hcoord (i : Fin n) :
      aeval (linearPolynomialConjugate T S H) (linearPolynomialMap T i) =
        linearPolynomialPullback T (H i) := by
    simp only [linearPolynomialMap, map_sum, map_mul, aeval_C, aeval_X]
    change ((T.map MvPolynomial.C) *ᵥ ((S.map MvPolynomial.C) *ᵥ
      (fun j => linearPolynomialPullback T (H j)))) i = _
    rw [Matrix.mulVec_mulVec, hTSC, Matrix.one_mulVec]
  have hcomp : (aeval (linearPolynomialConjugate T S H)).comp (aeval (linearPolynomialMap T)) =
      (aeval (linearPolynomialMap T)).comp (aeval H) := by
    apply MvPolynomial.algHom_ext
    intro i
    simpa only [AlgHom.comp_apply, aeval_X, linearPolynomialPullback] using hcoord i
  exact DFunLike.congr_fun hcomp F

/-- The full original evaluated normal transforms by the transpose
coordinate action, written as multiplication of a row by the source matrix. -/
theorem imageRelationNormal_linearPolynomialConjugate
    (T S : Matrix (Fin n) (Fin n) K) (hTS : T * S = 1)
    (H : Fin n → MvPolynomial (Fin n) K) (F : MvPolynomial (Fin n) K) :
    imageRelationNormal (linearPolynomialConjugate T S H) (linearPolynomialPullback T F) =
      (fun j => linearPolynomialPullback T (imageRelationNormal H F j)) ᵥ* T.map MvPolynomial.C := by
  have hder (j i : Fin n) : pderiv i (linearPolynomialMap T j) = MvPolynomial.C (T j i) := by
    change jac (linearPolynomialMap T) j i = _
    rw [jac_linearPolynomialMap]
    rfl
  funext i
  change aeval (linearPolynomialConjugate T S H) (pderiv i (linearPolynomialPullback T F)) = _
  rw [linearPolynomialPullback, pderiv_aeval, map_sum]
  simp only [map_mul, hder, aeval_C]
  change (∑ j, aeval (linearPolynomialConjugate T S H) (linearPolynomialPullback T (pderiv j F)) *
    MvPolynomial.C (T j i)) = _
  simp_rw [aeval_linearPolynomialPullback_conjugate T S hTS H]
  rfl

/-- The actual nonzero evaluated normal stays nonzero after conjugacy. -/
theorem imageRelationNormal_linearPolynomialConjugate_ne_zero
    (T S : Matrix (Fin n) (Fin n) K) (hTS : T * S = 1) (hST : S * T = 1)
    (H : Fin n → MvPolynomial (Fin n) K) (F : MvPolynomial (Fin n) K)
    (hn : imageRelationNormal H F ≠ 0) :
    imageRelationNormal (linearPolynomialConjugate T S H) (linearPolynomialPullback T F) ≠ 0 := by
  have hTSC : T.map (MvPolynomial.C : K →+* MvPolynomial (Fin n) K) * S.map MvPolynomial.C = 1 := by
    rw [← Matrix.map_mul, hTS]
    ext i j
    simp [Matrix.one_apply]
  intro hzero
  rw [imageRelationNormal_linearPolynomialConjugate T S hTS H F] at hzero
  have he := congrArg (fun v : Fin n → MvPolynomial (Fin n) K => v ᵥ* S.map MvPolynomial.C) hzero
  rw [Matrix.vecMul_vecMul, hTSC, Matrix.vecMul_one, Matrix.zero_vecMul] at he
  apply hn
  funext i
  apply (matrixPolynomialCoordinateEquiv T S hTS hST).injective
  change linearPolynomialPullback T (imageRelationNormal H F i) = linearPolynomialPullback T 0
  simpa only [linearPolynomialPullback, map_zero, Pi.zero_apply] using congrFun he i

/-- The same original irreducible homogeneous image relation supplies
an actual image-relation witness for the conjugated map. -/
noncomputable def ImageRelationWitness.linearConjugate
    (H : Fin n → MvPolynomial (Fin n) K) (I : ImageRelationWitness H)
    (T S : Matrix (Fin n) (Fin n) K) (hTS : T * S = 1) (hST : S * T = 1) :
    ImageRelationWitness (linearPolynomialConjugate T S H) where
  equation := linearPolynomialPullback T I.equation
  degree := I.degree
  degree_pos := I.degree_pos
  homogeneous := linearPolynomialPullback_homogeneous T I.equation I.homogeneous
  irreducible := by
    simpa only [matrixPolynomialCoordinateEquiv_apply] using
      I.irreducible.map (matrixPolynomialCoordinateEquiv T S hTS hST)
  vanishing := by
    rw [aeval_linearPolynomialPullback_conjugate T S hTS H, I.vanishing]
    exact map_zero (aeval (linearPolynomialMap T))
  normal_ne_zero := imageRelationNormal_linearPolynomialConjugate_ne_zero T S hTS hST H I.equation I.normal_ne_zero

/-- The transported witness retains the exact transformed equation. -/
theorem ImageRelationWitness.linearConjugate_equation
    (H : Fin n → MvPolynomial (Fin n) K) (I : ImageRelationWitness H)
    (T S : Matrix (Fin n) (Fin n) K) (hTS : T * S = 1) (hST : S * T = 1) :
    (I.linearConjugate H T S hTS hST).equation = linearPolynomialPullback T I.equation := rfl

/-- The degree in the original image-relation witness is retained. -/
theorem ImageRelationWitness.linearConjugate_degree
    (H : Fin n → MvPolynomial (Fin n) K) (I : ImageRelationWitness H)
    (T S : Matrix (Fin n) (Fin n) K) (hTS : T * S = 1) (hST : S * T = 1) :
    (I.linearConjugate H T S hTS hST).degree = I.degree := rfl

/-- The exact normal transport also holds in the original source field. -/
theorem rationalImageNormal_linearPolynomialConjugate
    (T S : Matrix (Fin 4) (Fin 4) K) (hTS : T * S = 1) (hST : S * T = 1)
    (H : Fin 4 → MvPolynomial (Fin 4) K) (F : MvPolynomial (Fin 4) K) :
    rationalImageNormal (linearPolynomialConjugate T S H) (linearPolynomialPullback T F) =
      (fun j => matrixSourceFractionEquiv T S hTS hST (rationalImageNormal H F j)) ᵥ*
        T.map (algebraMap K (FractionRing (MvPolynomial (Fin 4) K))) := by
  funext i
  simp only [rationalImageNormal, imageRelationNormal_linearPolynomialConjugate T S hTS H F,
    Matrix.vecMul, dotProduct, Matrix.map_apply, map_sum, map_mul,
    matrixSourceFractionEquiv_polynomial, ← MvPolynomial.algebraMap_eq,
    ← IsScalarTower.algebraMap_apply K (MvPolynomial (Fin 4) K) (FractionRing (MvPolynomial (Fin 4) K))]

/-- A common original normal annihilator becomes the fourth-axis
vertex when it is the fourth source column of the coordinate change. -/
theorem rationalImageNormal_conjugate_fixed_axis_of_common_vertex
    (T S : Matrix (Fin 4) (Fin 4) K) (hTS : T * S = 1) (hST : S * T = 1)
    (H : Fin 4 → MvPolynomial (Fin 4) K) (I : ImageRelationWitness H) (v : Fin 4 → K)
    (hcolumn : ∀ i, T i (Fin.last 3) = v i)
    (hv : rationalImageNormal H I.equation ⬝ᵥ
      (fun i => algebraMap K (FractionRing (MvPolynomial (Fin 4) K)) (v i)) = 0) :
    rationalImageNormal (linearPolynomialConjugate T S H)
      (I.linearConjugate H T S hTS hST).equation (Fin.last 3) = 0 := by
  rw [ImageRelationWitness.linearConjugate_equation,
    rationalImageNormal_linearPolynomialConjugate T S hTS hST H I.equation]
  change (∑ i, matrixSourceFractionEquiv T S hTS hST (rationalImageNormal H I.equation i) *
    algebraMap K (FractionRing (MvPolynomial (Fin 4) K)) (T i (Fin.last 3))) = 0
  simp_rw [hcolumn]
  let f := matrixSourceFractionEquiv T S hTS hST
  have hfix (c : K) : f (algebraMap K (FractionRing (MvPolynomial (Fin 4) K)) c) =
      algebraMap K (FractionRing (MvPolynomial (Fin 4) K)) c := f.commutes c
  simpa only [dotProduct, map_sum, map_mul, map_zero, hfix] using congrArg f hv

end DimensionFourDependence
