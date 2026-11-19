import DimensionFourDependence.RationalDerivative
import DimensionFourDependence.AlgebraicDerivation

/-! # The coordinate derivations of `K(Y)`

The rational partial derivatives are bundled as actual `K`-derivations,
determined by their values on the coordinates, and proved to commute.
-/

namespace DimensionFourDependence

open MvPolynomial

variable {K : Type*} [Field K] {n : ℕ}

/-- The `i`th coordinate of the rational function field. -/
noncomputable def rationalCoordinate (i : Fin n) : FractionRing (MvPolynomial (Fin n) K) :=
  algebraMap (MvPolynomial (Fin n) K) _ (X i)

/-- The coordinate partial derivative on the rational function field,
as a bundled derivation over `K`. -/
noncomputable def rationalPartial (i : Fin n) :
    Derivation K (FractionRing (MvPolynomial (Fin n) K)) (FractionRing (MvPolynomial (Fin n) K)) where
  toLinearMap :=
    { toFun := fracDeriv (K := K) i
      map_add' := fracDeriv_add i
      map_smul' := by
        intro c f
        simp only [RingHom.id_apply, Algebra.smul_def]
        rw [fracDeriv_mul, fracDeriv_algebraMap_field, mul_zero, add_zero] }
  map_one_eq_zero' := fracDeriv_one i
  leibniz' := by
    intro f g
    change fracDeriv (K := K) i (f * g) = f * fracDeriv i g + g * fracDeriv i f
    exact fracDeriv_mul i f g

theorem rationalPartial_polynomial (i : Fin n) (p : MvPolynomial (Fin n) K) :
    rationalPartial (K := K) i (algebraMap (MvPolynomial (Fin n) K) _ p) =
      algebraMap (MvPolynomial (Fin n) K) _ (pderiv i p) := fracDeriv_algebraMap i p

theorem rationalPartial_coordinate (i j : Fin n) :
    rationalPartial (K := K) i (rationalCoordinate (K := K) j) = if j = i then 1 else 0 := by
  by_cases hji : j = i
  · subst j
    simp [rationalCoordinate, rationalPartial_polynomial]
  · simp [rationalCoordinate, rationalPartial_polynomial, pderiv_X_of_ne hji, hji]

/-- A derivation of the rational function field is determined by its values
on the coordinate functions. -/
theorem derivation_ext_rational
    (D₁ D₂ : Derivation K (FractionRing (MvPolynomial (Fin n) K))
      (FractionRing (MvPolynomial (Fin n) K)))
    (hX : ∀ i, D₁ (rationalCoordinate i) = D₂ (rationalCoordinate i)) : D₁ = D₂ := by
  have hp : ∀ p : MvPolynomial (Fin n) K,
      D₁ (algebraMap (MvPolynomial (Fin n) K) _ p) = D₂ (algebraMap (MvPolynomial (Fin n) K) _ p) := by
    intro p
    induction p using MvPolynomial.induction_on with
    | C c =>
      rw [← MvPolynomial.algebraMap_eq, ← IsScalarTower.algebraMap_apply K (MvPolynomial (Fin n) K)]
      simp
    | add p q hp hq => simp only [map_add, hp, hq]
    | mul_X p i hp =>
      have hi := hX i
      change D₁ (algebraMap (MvPolynomial (Fin n) K) _ (X i)) =
        D₂ (algebraMap (MvPolynomial (Fin n) K) _ (X i)) at hi
      simp only [map_mul, Derivation.leibniz, hp, hi]
  ext f
  obtain ⟨p, q, _, rfl⟩ := IsFractionRing.div_surjective (A := MvPolynomial (Fin n) K) f
  rw [D₁.leibniz_div, D₂.leibniz_div, hp p, hp q]

/-- The coordinate partials commute on the entire rational function field. -/
theorem rationalPartials_commute (i j : Fin n) (f : FractionRing (MvPolynomial (Fin n) K)) :
    rationalPartial (K := K) i (rationalPartial (K := K) j f) =
      rationalPartial (K := K) j (rationalPartial (K := K) i f) := by
  have hz : ⁅rationalPartial (K := K) i, rationalPartial (K := K) j⁆ = 0 := by
    apply derivation_ext_rational (K := K)
    intro l
    simp only [Derivation.commutator_apply, rationalPartial_coordinate, Derivation.zero_apply]
    simp [apply_ite]
  have h := congrArg (fun D => D f) hz
  simpa only [Derivation.commutator_apply, Derivation.zero_apply, sub_eq_zero] using h

end DimensionFourDependence
