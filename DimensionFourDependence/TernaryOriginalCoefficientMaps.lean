import DimensionFourDependence.LinearConjugacyComposition
import DimensionFourDependence.ScalarExtendedMapHypotheses

/-! # Coefficient extension for actual ternary normalizing coordinates -/

namespace DimensionFourDependence

open MvPolynomial Matrix

universe u
set_option maxHeartbeats 2350000

variable {K E : Type u} [Field K] [Field E] [Algebra K E]
local notation "j" => (algebraMap K E)

/-- Polynomial evaluation commutes with the actual coefficient extension
and the corresponding original values of all the variables. -/
theorem polynomial_aeval_scalar_extension {σ : Type*} {A B : Type*} [CommSemiring A] [CommSemiring B]
    [Algebra K A] [Algebra E B] [Algebra K B] [IsScalarTower K E B]
    (φ : A →ₐ[K] B) (x : σ → A) (p : MvPolynomial σ K) :
    φ (aeval x p) = aeval (φ ∘ x) (MvPolynomial.map j p) := by
  simp only [MvPolynomial.aeval_def, MvPolynomial.eval₂_map]
  change φ.toRingHom (eval₂ (algebraMap K A) x p) = _
  rw [MvPolynomial.hom_eval₂]
  have h : φ.toRingHom.comp (algebraMap K A) = (algebraMap E B).comp j := by
    apply RingHom.ext
    intro a
    change φ (algebraMap K A a) = algebraMap E B (j a)
    rw [φ.commutes, ← IsScalarTower.algebraMap_apply K E B]
  rw [h]
  rfl

/-- Linear polynomial pullback and conjugacy commute with coefficient
extension of the actual original matrices and polynomials. -/
theorem ternary_linear_conjugate_scalar_extension
    (T S : Matrix (Fin 3) (Fin 3) K) (H : Fin 3 → MvPolynomial (Fin 3) K) :
    (fun i => MvPolynomial.map j (linearPolynomialConjugate T S H i)) =
      linearPolynomialConjugate (T.map j) (S.map j) (fun i => MvPolynomial.map j (H i)) := by
  let φ := MvPolynomial.mapAlgHom (σ := Fin 3) (Algebra.ofId K E)
  have hRows : φ ∘ linearPolynomialMap T = linearPolynomialMap (T.map j) := by
    funext i
    change MvPolynomial.map j (∑ k, C (T i k) * X k) = ∑ k, C (j (T i k)) * X k
    simp only [map_sum, map_mul, MvPolynomial.map_C, MvPolynomial.map_X]
  have hp (p : MvPolynomial (Fin 3) K) :
      MvPolynomial.map j (linearPolynomialPullback T p) =
        linearPolynomialPullback (T.map j) (MvPolynomial.map j p) := by
    change φ (aeval (linearPolynomialMap T) p) = _
    rw [polynomial_aeval_scalar_extension (E := E) φ, hRows]
    rfl
  funext i
  simp only [linearPolynomialConjugate, map_sum, map_mul, MvPolynomial.map_C, Matrix.map_apply, hp]

theorem ternary_nilpotent_jacobian_scalar_extension
    (H : Fin 3 → MvPolynomial (Fin 3) K) (h : IsNilpotent (jac H)) :
    IsNilpotent (jac (fun i => MvPolynomial.map j (H i))) := by
  have he : jac (fun i => MvPolynomial.map j (H i)) = (jac H).map (MvPolynomial.map j) := by
    funext i k
    exact MvPolynomial.pderiv_map (φ := j) (f := H i) (i := k)
  rw [he]
  exact h.map (MvPolynomial.map j).mapMatrix

end DimensionFourDependence
