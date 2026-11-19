import DimensionFourDependence.BoundaryIsotropicEquations

/-! # The second quadric obtained by eliminating the rank-one cubic

The polynomial is multiplied by six to retain integral numeric coefficients.
It is the cubic equation plus a linear multiple of the quadratic equation.
Its degree-two part gives the first equation in (4.3) at every actual
residue direction at infinity.
-/

namespace DimensionFourDependence

open MvPolynomial Matrix

variable {E : Type*} [Field E] {n : ℕ}

theorem linearFormPolynomial_homogeneous (a : Fin n → E) :
    (linearFormPolynomial a).IsHomogeneous 1 := by
  apply IsHomogeneous.sum
  intro i _
  exact isHomogeneous_C_mul_X _ _

/-- Six times the modified cubic after using the original quadratic
equation to eliminate its degree-three Hessian factor. -/
noncomputable def modifiedCubicFiberPolynomial (a v Λ : Fin n → E)
    (S : Matrix (Fin n) (Fin n) E) (q k : E) : MvPolynomial (Fin n) E :=
  C 6 * linearFormPolynomial v - C 3 * quadraticFormPolynomial S +
    C 2 * linearFormPolynomial Λ * linearFormPolynomial a -
    C (2 * q) * linearFormPolynomial Λ - C (6 * k)

theorem modifiedCubicFiberPolynomial_totalDegree (a v Λ : Fin n → E)
    (S : Matrix (Fin n) (Fin n) E) (q k : E) :
    (modifiedCubicFiberPolynomial a v Λ S q k).totalDegree ≤ 2 := by
  have hlin (c : E) (w : Fin n → E) : (C c * linearFormPolynomial w).totalDegree ≤ 1 := by
    have he := totalDegree_mul (C c) (linearFormPolynomial w)
    simp only [totalDegree_C, zero_add] at he
    exact he.trans (linearFormPolynomial_totalDegree w)
  have hquad : (C (3 : E) * quadraticFormPolynomial S).totalDegree ≤ 2 := by
    have he := totalDegree_mul (C (3 : E)) (quadraticFormPolynomial S)
    simp only [totalDegree_C, zero_add] at he
    exact he.trans (quadraticFormPolynomial_totalDegree S)
  have hprod : (C (2 : E) * linearFormPolynomial Λ * linearFormPolynomial a).totalDegree ≤ 2 := by
    exact (totalDegree_mul _ _).trans (add_le_add (hlin 2 Λ) (linearFormPolynomial_totalDegree a))
  unfold modifiedCubicFiberPolynomial
  apply (totalDegree_sub_C_le _ _).trans
  apply (totalDegree_sub _ _).trans
  apply max_le
  · apply (totalDegree_add _ _).trans
    apply max_le
    · exact (totalDegree_sub _ _).trans (max_le ((hlin 6 v).trans (by decide)) hquad)
    · exact hprod
  · exact (hlin (2 * q) Λ).trans (by decide)

variable [CharZero E]

/-- The second quadric belongs to the original quadratic-cubic ideal,
with the exact original coefficient arrays and invariant constants. -/
theorem modifiedCubicFiberPolynomial_elimination_identity
    (a v Λ : Fin n → E) (B S : Matrix (Fin n) (Fin n) E)
    (T : Fin n → Fin n → Fin n → E) (q k : E)
    (hfactor : cubicFormPolynomial T = linearFormPolynomial Λ * quadraticFormPolynomial B) :
    modifiedCubicFiberPolynomial a v Λ S q k =
      C 6 * cubicFiberPolynomial v S T k +
        C 2 * linearFormPolynomial Λ * quadraticFiberPolynomial a B q := by
  unfold modifiedCubicFiberPolynomial cubicFiberPolynomial quadraticFiberPolynomial
  rw [hfactor]
  have hhalf : (C (6 : E) : MvPolynomial (Fin n) E) * C ((2 : E)⁻¹) = C 3 := by
    rw [← map_mul]; norm_num
  have hsixth : (C (6 : E) : MvPolynomial (Fin n) E) * C ((6 : E)⁻¹) = 1 := by
    rw [← map_mul]; norm_num
  have htwohalf : (C (2 : E) : MvPolynomial (Fin n) E) * C ((2 : E)⁻¹) = 1 := by
    rw [← map_mul]; norm_num
  simp only [map_mul]
  linear_combination hhalf * quadraticFormPolynomial S +
    hsixth * (linearFormPolynomial Λ * quadraticFormPolynomial B) -
    htwohalf * (linearFormPolynomial Λ * quadraticFormPolynomial B)

omit [CharZero E] in
/-- Lower-degree terms disappear, retaining precisely the modified
cubic's quadratic expression in (4.3). -/
theorem modifiedCubicFiberPolynomial_leading_component
    (a v Λ : Fin n → E) (S : Matrix (Fin n) (Fin n) E) (q k : E) :
    homogeneousComponent 2 (modifiedCubicFiberPolynomial a v Λ S q k) =
      -C 3 * quadraticFormPolynomial S +
        C 2 * linearFormPolynomial Λ * linearFormPolynomial a := by
  have hl (w : Fin n → E) : homogeneousComponent 2 (linearFormPolynomial w) = 0 :=
    homogeneousComponent_eq_zero 2 _ (by have he := linearFormPolynomial_totalDegree w; omega)
  have hprod : (linearFormPolynomial Λ * linearFormPolynomial a).IsHomogeneous 2 :=
    (linearFormPolynomial_homogeneous Λ).mul (linearFormPolynomial_homogeneous a)
  have hc : homogeneousComponent 2 (C (6 * k) : MvPolynomial (Fin n) E) = 0 :=
    homogeneousComponent_eq_zero 2 _ (by simp only [totalDegree_C]; omega)
  unfold modifiedCubicFiberPolynomial
  rw [mul_assoc (C 2)]
  simp only [map_sub, map_add, homogeneousComponent_C_mul, hl, hc,
    homogeneousComponent_eq_self (quadraticFormPolynomial_homogeneous S),
    homogeneousComponent_eq_self hprod, mul_zero, zero_sub, sub_zero, neg_mul]

variable {O F κ : Type*} [CommRing O] [Field F] [Field κ]
    [Algebra E O] [Algebra E F] [Algebra O F] [IsScalarTower E O F] [Algebra E κ]

/-- The actual original quadratic and cubic fiber equations imply
the first equation of (4.3) at every residue direction at infinity.
No modified-quadric equation is an additional hypothesis. -/
theorem modified_cubic_fiber_boundary_equation
    (π : O →ₐ[E] κ) (hinj : Function.Injective (algebraMap O F))
    (x : Fin n → F) (s : F) (z : Option (Fin n) → O)
    (hz0 : algebraMap O F (z none) = s)
    (hz : ∀ i, algebraMap O F (z (some i)) = s * x i) (hres0 : π (z none) = 0)
    (a v Λ : Fin n → E) (B S : Matrix (Fin n) (Fin n) E)
    (T : Fin n → Fin n → Fin n → E) (q k : E)
    (hfactor : cubicFormPolynomial T = linearFormPolynomial Λ * quadraticFormPolynomial B)
    (hQ : aeval x (quadraticFiberPolynomial a B q) = 0)
    (hC : aeval x (cubicFiberPolynomial v S T k) = 0) :
    matrixBilinearPairing (S.map (algebraMap E κ)) (fun i => π (z (some i))) (fun i => π (z (some i))) -
      (2 / 3 : κ) * (∑ i, algebraMap E κ (Λ i) * π (z (some i))) *
        (∑ i, algebraMap E κ (a i) * π (z (some i))) = 0 := by
  let : CharZero κ := charZero_of_injective_algebraMap (algebraMap E κ).injective
  have hM : aeval x (modifiedCubicFiberPolynomial a v Λ S q k) = 0 := by
    rw [modifiedCubicFiberPolynomial_elimination_identity a v Λ B S T q k hfactor]
    simp only [map_add, map_mul, hQ, hC, mul_zero, zero_add]
  have he := leading_equation_residue_specialization π hinj x s z hz0 hz hres0
    (modifiedCubicFiberPolynomial a v Λ S q k) 2
    (modifiedCubicFiberPolynomial_totalDegree a v Λ S q k) hM
  rw [modifiedCubicFiberPolynomial_leading_component] at he
  simp only [map_add, map_mul, map_neg, aeval_C, linearFormPolynomial, quadraticFormPolynomial,
    map_sum, aeval_X, map_ofNat] at he
  change -(3 : κ) * matrixBilinearPairing (S.map (algebraMap E κ))
    (fun i => π (z (some i))) (fun i => π (z (some i))) +
      2 * (∑ i, algebraMap E κ (Λ i) * π (z (some i))) *
        (∑ i, algebraMap E κ (a i) * π (z (some i))) = 0 at he
  linear_combination -(3 : κ)⁻¹ * he

end DimensionFourDependence
