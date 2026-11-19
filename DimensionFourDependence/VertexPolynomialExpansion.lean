import DimensionFourDependence.Defs
import Mathlib.RingTheory.MvPolynomial.Homogeneous

/-! # Exact original coefficients in a distinguished vertex variable

The canonical option-variable equivalence retains the original
polynomial as a polynomial in the vertex coordinate. Evaluation gives
its entire coefficient expansion, and homogeneity determines the degree
of every coefficient in the remaining coordinates.
-/

namespace DimensionFourDependence

open MvPolynomial

set_option backward.isDefEq.respectTransparency false

variable {K A sigma : Type*} [Field K] [CommRing A] [Algebra K A]

/-- Evaluation retains the exact canonical vertex-variable expansion
of the original polynomial, with all its original coefficient polynomials. -/
theorem original_vertex_polynomial_evaluation_expansion
    (P : MvPolynomial (Option sigma) K) (x : sigma → A) (w : A) :
    aeval (fun j : Option sigma => j.elim w x) P =
      ∑ j ∈ (optionEquivLeft K sigma P).support,
        aeval x ((optionEquivLeft K sigma P).coeff j) * w ^ j := by
  classical
  let phi : Polynomial (MvPolynomial sigma K) →ₐ[K] A :=
    ((Polynomial.aeval w).restrictScalars K).comp (Polynomial.mapAlgHom (aeval x))
  have hC (Q : MvPolynomial sigma K) : phi (Polynomial.C Q) = aeval x Q := by
    change Polynomial.aeval w (Polynomial.map (aeval x).toRingHom (Polynomial.C Q)) = _
    rw [Polynomial.map_C, Polynomial.aeval_C]
    rfl
  have hX : phi Polynomial.X = w := by
    change Polynomial.aeval w (Polynomial.map (aeval x).toRingHom Polynomial.X) = w
    rw [Polynomial.map_X, Polynomial.aeval_X]
  have he : phi.comp (optionEquivLeft K sigma).toAlgHom =
      aeval (fun j : Option sigma => j.elim w x) := by
    apply MvPolynomial.algHom_ext
    intro j
    cases j with
    | none =>
      simpa only [AlgHom.comp_apply, AlgEquiv.toAlgHom_apply, aeval_X,
        optionEquivLeft_X_none, Option.elim_none] using hX
    | some i =>
      simpa only [AlgHom.comp_apply, AlgEquiv.toAlgHom_apply, aeval_X,
        optionEquivLeft_X_some, Option.elim_some] using hC (X i)
  rw [← DFunLike.congr_fun he P]
  simp only [AlgHom.comp_apply, AlgEquiv.toAlgHom_apply]
  calc
    phi (optionEquivLeft K sigma P) = phi
        (∑ j ∈ (optionEquivLeft K sigma P).support,
          Polynomial.C ((optionEquivLeft K sigma P).coeff j) * Polynomial.X ^ j) :=
      congrArg phi (Polynomial.as_sum_support_C_mul_X_pow _)
    _ = _ := by simp only [map_sum, map_mul, map_pow, hC, hX]

/-- The coefficient at vertex degree j of an original homogeneous
form of degree D is homogeneous of degree D-j in the other coordinates. -/
theorem original_vertex_coefficient_isHomogeneous [Finite sigma]
    (P : MvPolynomial (Option sigma) K) {D : ℕ} (hP : P.IsHomogeneous D)
    (j : ℕ) (hj : j ≤ D) :
    ((optionEquivLeft K sigma P).coeff j).IsHomogeneous (D - j) := by
  have hback : ((optionEquivLeft K sigma).symm (optionEquivLeft K sigma P)).IsHomogeneous D := by
    rwa [AlgEquiv.symm_apply_apply]
  exact IsHomogeneous.coeff_isHomogeneous_of_optionEquivLeft_symm hback j (D - j) (by omega)

end DimensionFourDependence
