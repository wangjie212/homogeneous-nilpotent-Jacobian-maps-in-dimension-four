import DimensionFourDependence.Tame

/-! # The cube-zero Jacobian assertion of Proposition 6.4 -/

namespace DimensionFourDependence.Shear

open MvPolynomial Matrix

variable {K : Type*} [Field K]

/-- A binary coefficient polynomial in the four-variable ring `K[x,y,z,t]`. -/
noncomputable def base4 (a : MvPolynomial (Fin 2) K) : MvPolynomial (Fin 4) K :=
  aeval ![X 2, X 3] a

noncomputable def invariant4 (a b : MvPolynomial (Fin 2) K) : MvPolynomial (Fin 4) K :=
  base4 a * X 0 + base4 b * X 1

noncomputable def parameter4 (a b : MvPolynomial (Fin 2) K)
    (f : MvPolynomial (Fin 3) K) : MvPolynomial (Fin 4) K :=
  aeval ![invariant4 a b, X 2, X 3] f

/-- The perturbation of `Ψ` in (6.8), with arbitrary polynomial coefficients. -/
noncomputable def perturbation4 (a b : MvPolynomial (Fin 2) K)
    (f : MvPolynomial (Fin 3) K) : Fin 4 → MvPolynomial (Fin 4) K :=
  ![base4 b * parameter4 a b f, -(base4 a * parameter4 a b f), 0, 0]

theorem pderiv_base4_active (a : MvPolynomial (Fin 2) K) (j : Fin 4)
    (hj2 : j ≠ 2) (hj3 : j ≠ 3) : pderiv j (base4 a) = 0 := by
  rw [base4, pderiv_aeval]
  simp [Fin.sum_univ_succ, pderiv_X, Pi.single_apply, Ne.symm hj2, Ne.symm hj3]

theorem pderiv_parameter4_x (a b : MvPolynomial (Fin 2) K)
    (f : MvPolynomial (Fin 3) K) :
    pderiv 0 (parameter4 a b f) =
      aeval ![invariant4 a b, X 2, X 3] (pderiv 0 f) * base4 a := by
  rw [parameter4, pderiv_aeval]
  simp [Fin.sum_univ_succ, invariant4, pderiv_mul,
    pderiv_base4_active _ 0 (by decide) (by decide)]

theorem pderiv_parameter4_y (a b : MvPolynomial (Fin 2) K)
    (f : MvPolynomial (Fin 3) K) :
    pderiv 1 (parameter4 a b f) =
      aeval ![invariant4 a b, X 2, X 3] (pderiv 0 f) * base4 b := by
  rw [parameter4, pderiv_aeval]
  simp [Fin.sum_univ_succ, invariant4, pderiv_mul,
    pderiv_base4_active _ 1 (by decide) (by decide)]

/-- The block form in the proof of Proposition 6.4; the upper-right block
is unrestricted. -/
def jacobianBlock {R : Type*} [CommRing R] (a b s c₀ c₁ d₀ d₁ : R) :
    Matrix (Fin 4) (Fin 4) R :=
  ![![b * s * a, b * s * b, c₀, c₁],
    ![-(a * s * a), -(a * s * b), d₀, d₁],
    ![0, 0, 0, 0], ![0, 0, 0, 0]]

theorem jacobianBlock_cube {R : Type*} [CommRing R] (a b s c₀ c₁ d₀ d₁ : R) :
    jacobianBlock a b s c₀ c₁ d₀ d₁ ^ 3 = 0 := by
  rw [pow_three]
  ext i j
  change (∑ k : Fin 4, jacobianBlock a b s c₀ c₁ d₀ d₁ i k *
    (∑ l : Fin 4, jacobianBlock a b s c₀ c₁ d₀ d₁ k l *
      jacobianBlock a b s c₀ c₁ d₀ d₁ l j)) = 0
  fin_cases i <;> fin_cases j <;>
    simp [jacobianBlock, Fin.sum_univ_succ] <;> ring

theorem jac_perturbation4_block (a b : MvPolynomial (Fin 2) K)
    (f : MvPolynomial (Fin 3) K) :
    jac (perturbation4 a b f) =
      jacobianBlock (base4 a) (base4 b)
        (aeval ![invariant4 a b, X 2, X 3] (pderiv 0 f))
        (pderiv 2 (perturbation4 a b f 0)) (pderiv 3 (perturbation4 a b f 0))
        (pderiv 2 (perturbation4 a b f 1)) (pderiv 3 (perturbation4 a b f 1)) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [jac, jacobianBlock, perturbation4, pderiv_mul,
      pderiv_base4_active _ 0 (by decide) (by decide),
      pderiv_base4_active _ 1 (by decide) (by decide),
      pderiv_parameter4_x, pderiv_parameter4_y, mul_assoc]

/-- The full four-variable perturbation Jacobian has cube zero, with no
homogeneity or coprimality restrictions on `a,b,f`. -/
theorem jac_perturbation4_cube (a b : MvPolynomial (Fin 2) K)
    (f : MvPolynomial (Fin 3) K) : jac (perturbation4 a b f) ^ 3 = 0 := by
  rw [jac_perturbation4_block]
  exact jacobianBlock_cube _ _ _ _ _ _ _

end DimensionFourDependence.Shear
