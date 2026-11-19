import DimensionFourDependence.ActivePencilPerturbationConjugacy
import DimensionFourDependence.BinaryPencilScalarShearIdentity

/-! # Lemma 6.9 in the full four-variable polynomial algebra -/

namespace DimensionFourDependence.Shear

open Matrix MvPolynomial

set_option maxHeartbeats 1100000

variable {K : Type*} [Field K]
local notation "R₂" => MvPolynomial (Fin 2) K
local notation "R₄" => MvPolynomial (Fin 4) K
local notation "M₂" => Matrix (Fin 2) (Fin 2) K

/-- An active coordinate change realizes the new pencil basis and
multiplies the scalar by the determinant of that coordinate change. -/
theorem lemma_6_9 (T S : M₂) (hTS : T * S = 1) (hST : S * T = 1)
    (a b : R₂) (c : K) :
    let a' := C (T 0 0) * a + C (T 1 0) * b
    let b' := C (T 0 1) * a + C (T 1 1) * b
    linearPolynomialConjugate (activePencilMatrix T) (activePencilMatrix S)
        (perturbation4 a b (C c * X 0)) =
      perturbation4 a' b' (C (c * S.det) * X 0) := by
  let a' := C (T 0 0) * a + C (T 1 0) * b
  let b' := C (T 0 1) * a + C (T 1 1) * b
  let D := T.map (C : K →+* R₄)
  let M := S.map (C : K →+* R₄)
  let x : R₄ := X 0
  let y : R₄ := X 1
  let x' := D 0 0 * x + D 0 1 * y
  let y' := D 1 0 * x + D 1 1 * y
  let L := base4 a * x' + base4 b * y'
  let P : R₄ →ₐ[K] R₄ := aeval (linearPolynomialMap (activePencilMatrix T))
  let H := perturbation4 a b (C c * X 0)
  have hz2 : H 2 = 0 := rfl
  have hz3 : H 3 = 0 := rfl
  have hP (u : R₂) : P (base4 u) = base4 u := activePencilMatrix_pullback_base T u
  have hC (k : K) : P (C k) = C k := P.commutes k
  have hX (i : Fin 2) : P (X i.castSucc.castSucc) =
      D i 0 * x + D i 1 * y := by
    change linearPolynomialPullback (activePencilMatrix T) (X i.castSucc.castSucc) = _
    rw [activePencilMatrix_pullback_active, Fin.sum_univ_two]
    rfl
  have hx : P (X 0) = x' := hX 0
  have hy : P (X 1) = y' := hX 1
  have hinv : P (invariant4 a b) = L := by
    simp only [invariant4, map_add, map_mul, hP, hx, hy, L]
  have hp (j : Fin 2) : linearPolynomialPullback (activePencilMatrix T) (H j.castSucc.castSucc) =
      ![C c * base4 b * L, -(C c * base4 a * L)] j := by
    change P (perturbation4 a b (C c * X 0) j.castSucc.castSucc) = _
    rw [scalar_linear_shear_perturbation]
    fin_cases j
    · change P (C c * base4 b * invariant4 a b) = C c * base4 b * L
      simp only [map_mul, hC, hP, hinv]
    · change P (-(C c * base4 a * invariant4 a b)) = -(C c * base4 a * L)
      simp only [map_neg, map_mul, hC, hP, hinv]
  have hDM : D * M = 1 := by
    change (C : K →+* R₄).mapMatrix T * (C : K →+* R₄).mapMatrix S = 1
    rw [← map_mul, hTS, map_one]
  have hMD : M * D = 1 := by
    change (C : K →+* R₄).mapMatrix S * (C : K →+* R₄).mapMatrix T = 1
    rw [← map_mul, hST, map_one]
  have hdet : M.det = C S.det := ((C : K →+* R₄).map_det S).symm
  let B : R₂ →ₐ[K] R₄ := aeval ![X 2, X 3]
  have hB (k : K) : B (C k) = C k := B.commutes k
  have ha' : D 0 0 * base4 a + D 1 0 * base4 b = base4 a' := by
    change C (T 0 0) * B a + C (T 1 0) * B b = B (C (T 0 0) * a + C (T 1 0) * b)
    simp only [map_add, map_mul, hB]
  have hb' : D 0 1 * base4 a + D 1 1 * base4 b = base4 b' := by
    change C (T 0 1) * B a + C (T 1 1) * B b = B (C (T 0 1) * a + C (T 1 1) * b)
    simp only [map_add, map_mul, hB]
  have hpair := binary_pencil_scalar_shear_conjugate D M hDM hMD (base4 a) (base4 b) (C c) x y
  change M *ᵥ ![C c * base4 b * L, -(C c * base4 a * L)] =
      ![(C c * M.det) * (D 0 1 * base4 a + D 1 1 * base4 b) *
          ((D 0 0 * base4 a + D 1 0 * base4 b) * x + (D 0 1 * base4 a + D 1 1 * base4 b) * y),
        -((C c * M.det) * (D 0 0 * base4 a + D 1 0 * base4 b) *
          ((D 0 0 * base4 a + D 1 0 * base4 b) * x + (D 0 1 * base4 a + D 1 1 * base4 b) * y))] at hpair
  rw [hdet, ha', hb', ← (C : K →+* R₄).map_mul] at hpair
  have hactive (i : Fin 2) :
      linearPolynomialConjugate (activePencilMatrix T) (activePencilMatrix S) H i.castSucc.castSucc =
        perturbation4 a' b' (C (c * S.det) * X 0) i.castSucc.castSucc := by
    rw [activePencilMatrix_conjugate_active T S H hz2 hz3, scalar_linear_shear_perturbation]
    simp only [hp]
    have hi := congrFun hpair i
    fin_cases i <;> exact hi
  change linearPolynomialConjugate (activePencilMatrix T) (activePencilMatrix S) H =
    perturbation4 a' b' (C (c * S.det) * X 0)
  funext i
  fin_cases i
  · exact hactive 0
  · exact hactive 1
  · exact activePencilMatrix_conjugate_penultimate T S H hz2 hz3
  · exact activePencilMatrix_conjugate_last T S H hz3

end DimensionFourDependence.Shear
