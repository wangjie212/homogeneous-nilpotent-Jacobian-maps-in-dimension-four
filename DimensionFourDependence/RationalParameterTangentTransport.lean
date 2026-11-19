import DimensionFourDependence.NormalizedJacobianSimplePole
import DimensionFourDependence.Homogeneous

/-! # Differentiating the original rational parameter on the cone

Equality of the rational functions modulo the cone equation implies
transport of their actual differentials on the cone tangent hyperplane.
-/

namespace DimensionFourDependence

open MvPolynomial Matrix

variable {K κ : Type*} [Field K] [Field κ] {n : ℕ}

/-- The polynomial gradient evaluated by the specified original-source map. -/
noncomputable def mappedPolynomialGradient (f : MvPolynomial (Fin n) K →+* κ)
    (p : MvPolynomial (Fin n) K) : Fin n → κ := fun j => f (pderiv j p)

/-- The differential of an actual rational function `p/q` at the given
point, represented by its original polynomial numerator and denominator. -/
noncomputable def polynomialRatioCovector (f : MvPolynomial (Fin n) K →+* κ)
    (p q : MvPolynomial (Fin n) K) : Fin n → κ :=
  fun j => (f (pderiv j p) * f q - f p * f (pderiv j q)) / (f q) ^ 2

theorem mappedPolynomialGradient_product_pairing
    (f : MvPolynomial (Fin n) K →+* κ) (p q : MvPolynomial (Fin n) K)
    (v : Fin n → κ) :
    mappedPolynomialGradient f (p * q) ⬝ᵥ v =
      f q * (mappedPolynomialGradient f p ⬝ᵥ v) +
        f p * (mappedPolynomialGradient f q ⬝ᵥ v) := by
  simp only [mappedPolynomialGradient, pderiv_mul, map_add, map_mul,
    dotProduct, add_mul, Finset.sum_add_distrib, Finset.mul_sum]
  congr 1 <;> apply Finset.sum_congr rfl <;> intro i _ <;> ring

theorem mappedPolynomialGradient_sub_pairing
    (f : MvPolynomial (Fin n) K →+* κ) (p q : MvPolynomial (Fin n) K)
    (v : Fin n → κ) :
    mappedPolynomialGradient f (p - q) ⬝ᵥ v =
      mappedPolynomialGradient f p ⬝ᵥ v - mappedPolynomialGradient f q ⬝ᵥ v := by
  simp only [mappedPolynomialGradient, map_sub, dotProduct, sub_mul, Finset.sum_sub_distrib]

/-- The original polynomial substitution supplies the full directional
chain rule at the actual residue point. -/
theorem mappedPolynomialGradient_composition_pairing
    (f : MvPolynomial (Fin n) K →+* κ)
    (P : Fin n → MvPolynomial (Fin n) K) (p : MvPolynomial (Fin n) K)
    (v : Fin n → κ) :
    mappedPolynomialGradient f (aeval P p) ⬝ᵥ v =
      mappedPolynomialGradient (f.comp (aeval P).toRingHom) p ⬝ᵥ
        ((jac P).map f *ᵥ v) := by
  rw [dotProduct_mulVec]
  congr 1
  funext j
  simp only [mappedPolynomialGradient, pderiv_aeval, map_sum, map_mul,
    vecMul, dotProduct, jac, Matrix.of_apply, Matrix.map_apply, RingHom.comp_apply,
    AlgHom.toRingHom_eq_coe, RingHom.coe_coe]

theorem polynomialRatioCovector_pairing
    (f : MvPolynomial (Fin n) K →+* κ) (p q : MvPolynomial (Fin n) K)
    (v : Fin n → κ) :
    polynomialRatioCovector f p q ⬝ᵥ v =
      (f q * (mappedPolynomialGradient f p ⬝ᵥ v) -
        f p * (mappedPolynomialGradient f q ⬝ᵥ v)) / (f q) ^ 2 := by
  simp only [polynomialRatioCovector, mappedPolynomialGradient, dotProduct,
    sub_mul, div_mul_eq_mul_div, Finset.sum_sub_distrib, ← Finset.sum_div, Finset.mul_sum]
  congr 2 <;> apply Finset.sum_congr rfl <;> intro i _ <;> ring

/-- A homogeneous degree-zero rational parameter annihilates the
radial vector, including at the target point of the restriction. -/
theorem polynomialRatioCovector_radial_eq_zero
    (f : MvPolynomial (Fin n) K →+* κ) (p q : MvPolynomial (Fin n) K)
    {d : ℕ} (hp : p.IsHomogeneous d) (hq : q.IsHomogeneous d) :
    polynomialRatioCovector f p q ⬝ᵥ (fun i => f (X i)) = 0 := by
  have he (z : MvPolynomial (Fin n) K) (hz : z.IsHomogeneous d) :
      mappedPolynomialGradient f z ⬝ᵥ (fun i => f (X i)) = (d : κ) * f z := by
    have h := congrArg f hz.sum_X_mul_pderiv
    simp only [map_sum, map_mul, nsmul_eq_mul, map_natCast] at h
    simpa only [mappedPolynomialGradient, dotProduct, mul_comm] using h
  rw [polynomialRatioCovector_pairing, he p hp, he q hq]
  have hz : f q * ((d : κ) * f p) - f p * ((d : κ) * f q) = 0 := by ring
  rw [hz, zero_div]

/-- Equality of the actual rational parameter on the cone gives
differential transport on its actual tangent hyperplane. Divisibility,
rather than equality off the cone, suffices. -/
theorem polynomial_ratio_preservation_implies_tangent_transport
    (f : MvPolynomial (Fin n) K →+* κ)
    (P : Fin n → MvPolynomial (Fin n) K)
    (R p q : MvPolynomial (Fin n) K)
    (hR : f R = 0) (hq : f q ≠ 0) (hqP : f (aeval P q) ≠ 0)
    (hpreserve : R ∣ aeval P p * q - p * aeval P q)
    (v : Fin n → κ) (hv : mappedPolynomialGradient f R ⬝ᵥ v = 0) :
    polynomialRatioCovector (f.comp (aeval P).toRingHom) p q ⬝ᵥ
        ((jac P).map f *ᵥ v) = polynomialRatioCovector f p q ⬝ᵥ v := by
  obtain ⟨C, hC⟩ := hpreserve
  have hcross : f (aeval P p) * f q - f p * f (aeval P q) = 0 := by
    have h := congrArg f hC
    simpa only [map_sub, map_mul, hR, zero_mul] using h
  have hdiff := congrArg (fun z => mappedPolynomialGradient f z ⬝ᵥ v) hC
  rw [mappedPolynomialGradient_sub_pairing, mappedPolynomialGradient_product_pairing,
    mappedPolynomialGradient_product_pairing, mappedPolynomialGradient_product_pairing,
    hR, hv] at hdiff
  simp only [zero_mul, mul_zero, add_zero] at hdiff
  rw [polynomialRatioCovector_pairing, polynomialRatioCovector_pairing,
    ← mappedPolynomialGradient_composition_pairing,
    ← mappedPolynomialGradient_composition_pairing]
  simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe]
  field_simp
  linear_combination f q * f (aeval P q) * hdiff -
    (f q * (mappedPolynomialGradient f (aeval P q) ⬝ᵥ v) +
      f (aeval P q) * (mappedPolynomialGradient f q ⬝ᵥ v)) * hcross

end DimensionFourDependence
