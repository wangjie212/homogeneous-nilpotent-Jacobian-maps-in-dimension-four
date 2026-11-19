import DimensionFourDependence.ExtensionFieldProjectivePoint
import DimensionFourDependence.CubicRadialBaseChange

/-! # Leading quadratic and cubic equations of a residue direction at infinity -/

namespace DimensionFourDependence

open MvPolynomial

variable {E A σ : Type*} [Field E] [CommRing A] [Algebra E A]

/-- At infinity, degree-`d` homogenization evaluates to the degree-`d`
homogeneous component, including when that component is zero. -/
theorem projectiveHomogenize_aeval_at_infinity
    (P : MvPolynomial σ E) (d : ℕ) (hd : P.totalDegree ≤ d) (x : σ → A) :
    aeval (fun j : Option σ => j.elim 0 x) (projectiveHomogenize P d) =
      aeval x (homogeneousComponent d P) := by
  classical
  rw [homogeneousComponent_apply]
  simp only [projectiveHomogenize, map_sum, map_mul, map_pow, aeval_rename,
    Function.comp_def, Option.elim_some, aeval_X, Option.elim_none, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro m hm
  have hmdeg : m.degree ≤ d := by
    have he := (le_totalDegree hm).trans hd
    simpa only [Finsupp.degree_apply, Finsupp.sum] using he
  by_cases he : m.degree = d
  · simp [he]
  · have hpos : d - m.degree ≠ 0 := by omega
    simp [he, hpos]

variable {O F κ : Type*} [CommRing O] [Field F] [CommRing κ]
    [Algebra E O] [Algebra E F] [Algebra O F] [IsScalarTower E O F] [Algebra E κ]

/-- An affine equation's leading part vanishes at every normalized
residue direction whose homogenizing coordinate is zero. -/
theorem leading_equation_residue_specialization
    (π : O →ₐ[E] κ) (hinj : Function.Injective (algebraMap O F))
    (x : σ → F) (s : F) (z : Option σ → O)
    (hz0 : algebraMap O F (z none) = s)
    (hz : ∀ i, algebraMap O F (z (some i)) = s * x i) (hres0 : π (z none) = 0)
    (P : MvPolynomial σ E) (d : ℕ) (hd : P.totalDegree ≤ d) (hzero : aeval x P = 0) :
    aeval (fun i => π (z (some i))) (homogeneousComponent d P) = 0 := by
  have he := homogenized_equation_residue_specialization π hinj x s z hz0 hz P d hd hzero
  have hf : (fun j => π (z j)) =
      (fun j : Option σ => j.elim 0 (fun i => π (z (some i)))) := by
    funext j
    cases j <;> simp only [Option.elim_none, Option.elim_some, hres0]
  rw [hf, projectiveHomogenize_aeval_at_infinity P d hd] at he
  exact he

variable {n : ℕ}

theorem quadraticFormPolynomial_homogeneous (T : Matrix (Fin n) (Fin n) E) :
    (quadraticFormPolynomial T).IsHomogeneous 2 := by
  unfold quadraticFormPolynomial
  apply IsHomogeneous.sum
  intro i _
  apply IsHomogeneous.sum
  intro j _
  exact (isHomogeneous_C_mul_X (T i j) i).mul (isHomogeneous_X (R := E) j)

theorem cubicFormPolynomial_homogeneous (T : Fin n → Fin n → Fin n → E) :
    (cubicFormPolynomial T).IsHomogeneous 3 := by
  unfold cubicFormPolynomial
  apply IsHomogeneous.sum
  intro i _
  apply IsHomogeneous.sum
  intro j _
  apply IsHomogeneous.sum
  intro k _
  exact ((isHomogeneous_C_mul_X (T i j k) i).mul (isHomogeneous_X (R := E) j)).mul (isHomogeneous_X (R := E) k)

theorem quadraticFiberPolynomial_leading_component
    (a : Fin n → E) (T : Matrix (Fin n) (Fin n) E) (q : E) :
    homogeneousComponent 2 (quadraticFiberPolynomial a T q) =
      C ((2 : E)⁻¹) * quadraticFormPolynomial T := by
  have hl : homogeneousComponent 2 (linearFormPolynomial a) = 0 :=
    homogeneousComponent_eq_zero 2 (linearFormPolynomial a) (by have he := linearFormPolynomial_totalDegree a; omega)
  have hq : homogeneousComponent 2 (C q : MvPolynomial (Fin n) E) = 0 :=
    homogeneousComponent_eq_zero 2 (C q) (by simp only [totalDegree_C]; omega)
  simp only [quadraticFiberPolynomial, map_sub, map_add, homogeneousComponent_C_mul,
    hl, homogeneousComponent_eq_self (quadraticFormPolynomial_homogeneous T), hq, zero_add, sub_zero]

theorem cubicFiberPolynomial_leading_component
    (a : Fin n → E) (S : Matrix (Fin n) (Fin n) E)
    (T : Fin n → Fin n → Fin n → E) (k : E) :
    homogeneousComponent 3 (cubicFiberPolynomial a S T k) =
      -(C ((6 : E)⁻¹) * cubicFormPolynomial T) := by
  have hl : homogeneousComponent 3 (linearFormPolynomial a) = 0 :=
    homogeneousComponent_eq_zero 3 (linearFormPolynomial a) (by have he := linearFormPolynomial_totalDegree a; omega)
  have hS : homogeneousComponent 3 (quadraticFormPolynomial S) = 0 :=
    homogeneousComponent_eq_zero 3 (quadraticFormPolynomial S) (by have he := quadraticFormPolynomial_totalDegree S; omega)
  have hk : homogeneousComponent 3 (C k : MvPolynomial (Fin n) E) = 0 :=
    homogeneousComponent_eq_zero 3 (C k) (by simp only [totalDegree_C]; omega)
  simp only [cubicFiberPolynomial, map_sub, homogeneousComponent_C_mul, hl, hS,
    homogeneousComponent_eq_self (cubicFormPolynomial_homogeneous T), hk, mul_zero, sub_zero, zero_sub]

end DimensionFourDependence
