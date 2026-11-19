import DimensionFourDependence.HomogenizedParameterPencil
import DimensionFourDependence.ImageEquationWitness

/-! # Every actual source pencil hypersurface maps into its specified projective image line -/

namespace DimensionFourDependence

open MvPolynomial

set_option maxHeartbeats 3000000

variable {K : Type*} [Field K] {n : ℕ}
local notation "R₀" => MvPolynomial (Fin n) K
local notation "F₀" => FractionRing (MvPolynomial (Fin n) K)

/-- A coprime source pencil retains its denominator coprime to each
literal member, without a generic-parameter assumption. -/
theorem reduced_source_pencil_member_isRelPrime_denominator
    (p q : R₀) (hrel : IsRelPrime p q) (a : K) : IsRelPrime (p - C a * q) q :=
  IsRelPrime.sub_mul_right_left_iff.mpr hrel

/-- A polynomial projective parametrization supplies exact divisibility
of the original cross equations by every literal source pencil member.
The common scalar may be an arbitrary source rational function: no
polynomial scalar or removal of an open subset is assumed. -/
theorem reduced_source_pencil_divides_original_projective_cross_equations
    (H : Fin n → R₀) (p q : R₀) (hq : q ≠ 0) (hrel : IsRelPrime p q)
    (v : Fin n → Polynomial K) (r : F₀)
    (hrep : ∀ i, algebraMap R₀ F₀ (H i) =
      r * Polynomial.aeval (algebraMap R₀ F₀ p / algebraMap R₀ F₀ q) (v i))
    (a : K) (i j : Fin n) :
    p - C a * q ∣ C ((v j).eval a) * H i - C ((v i).eval a) * H j := by
  classical
  let N := Finset.univ.sup (fun i => (v i).natDegree)
  have hN (k : Fin n) : (v k).natDegree ≤ N :=
    Finset.le_sup (f := fun i => (v i).natDegree) (Finset.mem_univ k)
  let W : Fin n → R₀ := fun k => homogeneousParameterPolynomialValue (v k) N p q
  let f : R₀ →ₐ[K] F₀ := IsScalarTower.toAlgHom K R₀ F₀
  have hqF : f q ≠ 0 := by
    exact fun hz => hq (IsFractionRing.injective R₀ F₀ (hz.trans (map_zero _).symm))
  have hW (k : Fin n) : f (W k) = f q ^ N * Polynomial.aeval (f p / f q) (v k) := by
    rw [homogeneousParameterPolynomialValue_algHom,
      homogeneousParameterPolynomialValue_fraction (v k) (hN k) _ _ hqF]
  have hrepF (k : Fin n) : f (H k) = r * Polynomial.aeval (f p / f q) (v k) := hrep k
  have hcross : H i * W j - H j * W i = 0 := by
    apply IsFractionRing.injective R₀ F₀
    change f (H i * W j - H j * W i) = f 0
    simp only [map_sub, map_mul, map_zero, hW]
    rw [hrepF, hrepF]
    ring
  have hdiv := dvd_sub
    (dvd_mul_of_dvd_right (source_pencil_divides_homogeneous_parameter_remainder (v j) (hN j) p q a) (H i))
    (dvd_mul_of_dvd_right (source_pencil_divides_homogeneous_parameter_remainder (v i) (hN i) p q a) (H j))
  have he : H i * (W j - q ^ N * C ((v j).eval a)) -
      H j * (W i - q ^ N * C ((v i).eval a)) =
      -(q ^ N * (C ((v j).eval a) * H i - C ((v i).eval a) * H j)) := by
    linear_combination hcross
  change p - C a * q ∣ H i * (W j - q ^ N * C ((v j).eval a)) -
    H j * (W i - q ^ N * C ((v i).eval a)) at hdiv
  rw [he] at hdiv
  have hdiv' := dvd_neg.mp hdiv
  exact (reduced_source_pencil_member_isRelPrime_denominator p q hrel a).pow_right.dvd_of_dvd_mul_left hdiv'

/-- Every point of the entire literal source pencil hypersurface
has original image collinear with the actual parameter value. -/
theorem reduced_source_pencil_zero_locus_maps_into_parameter_line
    (H : Fin n → R₀) (p q : R₀) (hq : q ≠ 0) (hrel : IsRelPrime p q)
    (v : Fin n → Polynomial K) (r : F₀)
    (hrep : ∀ i, algebraMap R₀ F₀ (H i) =
      r * Polynomial.aeval (algebraMap R₀ F₀ p / algebraMap R₀ F₀ q) (v i))
    (a : K) (z : Fin n → K) (hz : aeval z (p - C a * q) = 0) (i j : Fin n) :
    aeval z (H i) * (v j).eval a = aeval z (H j) * (v i).eval a := by
  obtain ⟨b, hb⟩ := reduced_source_pencil_divides_original_projective_cross_equations
    H p q hq hrel v r hrep a i j
  have he := congrArg (aeval z) hb
  simp only [map_sub, map_mul, aeval_C, Algebra.algebraMap_self, RingHom.id_apply,
    hz, zero_mul] at he
  simpa only [mul_comm] using sub_eq_zero.mp he

end DimensionFourDependence
