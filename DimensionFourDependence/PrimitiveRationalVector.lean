import DimensionFourDependence.Defs

/-! # Primitive polynomial presentations of actual rational-function vectors

Clear the finitely many denominators in the actual rational-function
field and extract the polynomial gcd. The remaining actual vector is
primitive, and the original vector is its nonzero rational scalar multiple.
Algebra maps evaluate these polynomial entries at the image of the parameter.
-/

namespace DimensionFourDependence

variable {K : Type*} [Field K] {n : ℕ}

/-- Every nonzero polynomial vector has a nonzero scalar polynomial
factor and a primitive polynomial-vector quotient. -/
theorem polynomial_vector_primitive_factorization
    (A : Fin n → Polynomial K) (hA : A ≠ 0) :
    ∃ (d : Polynomial K) (v : Fin n → Polynomial K), d ≠ 0 ∧ v ≠ 0 ∧
      (∀ r : Polynomial K, (∀ i, r ∣ v i) → IsUnit r) ∧ ∀ i, A i = d * v i := by
  classical
  obtain ⟨i, hi⟩ : ∃ i, A i ≠ 0 := by
    simpa only [ne_eq, funext_iff, Pi.zero_apply, not_forall] using hA
  obtain ⟨v, hv, hgcd⟩ := Finset.extract_gcd (s := Finset.univ) A ⟨i, Finset.mem_univ i⟩
  let d := Finset.univ.gcd A
  have hrep (j : Fin n) : A j = d * v j := hv j (Finset.mem_univ j)
  have hd : d ≠ 0 := by
    intro hz
    apply hi
    rw [hrep i, hz, zero_mul]
  have hv0 : v ≠ 0 := by
    intro hz
    apply hi
    rw [hrep i, hz]
    simp
  refine ⟨d, v, hd, hv0, ?_, hrep⟩
  intro r hr
  have hrg : r ∣ Finset.univ.gcd v := Finset.dvd_gcd (fun j _ => hr j)
  rw [hgcd] at hrg
  exact isUnit_of_dvd_one hrg

/-- Every actual nonzero vector in the one-variable rational-function
field has an actual primitive polynomial representative over the original field. -/
theorem rational_vector_primitive_polynomial_presentation
    (b : Fin n → RatFunc K) (hb : b ≠ 0) :
    ∃ v : Fin n → Polynomial K, v ≠ 0 ∧
      (∀ r : Polynomial K, (∀ i, r ∣ v i) → IsUnit r) ∧
      ∃ c : RatFunc K, c ≠ 0 ∧ ∀ i, b i = c * algebraMap (Polynomial K) (RatFunc K) (v i) := by
  classical
  obtain ⟨D, hD⟩ := IsLocalization.exist_integer_multiples_of_finite
    (nonZeroDivisors (Polynomial K)) b
  choose A hA using hD
  have hD0 : (D : Polynomial K) ≠ 0 := mem_nonZeroDivisors_iff_ne_zero.mp D.property
  have hDF : algebraMap (Polynomial K) (RatFunc K) (D : Polynomial K) ≠ 0 := by
    simpa only [map_zero] using (IsFractionRing.injective (Polynomial K) (RatFunc K)).ne hD0
  have hA0 : A ≠ 0 := by
    intro hz
    apply hb
    funext i
    have he := hA i
    rw [hz] at he
    simp only [Pi.zero_apply, map_zero, Algebra.smul_def] at he
    exact (mul_eq_zero.mp he.symm).resolve_left hDF
  obtain ⟨d, v, hd, hv, hprimitive, hrep⟩ := polynomial_vector_primitive_factorization A hA0
  have hdF : algebraMap (Polynomial K) (RatFunc K) d ≠ 0 := by
    simpa only [map_zero] using (IsFractionRing.injective (Polynomial K) (RatFunc K)).ne hd
  refine ⟨v, hv, hprimitive, algebraMap (Polynomial K) (RatFunc K) d /
    algebraMap (Polynomial K) (RatFunc K) (D : Polynomial K), div_ne_zero hdF hDF, ?_⟩
  intro i
  rw [div_mul_eq_mul_div]
  apply (eq_div_iff hDF).mpr
  have he := hA i
  simp only [Algebra.smul_def] at he
  rw [mul_comm, ← he, hrep i, map_mul]

variable {F : Type*} [Field F] [Algebra K F]

/-- An actual rational-function-field algebra map evaluates each
polynomial at the image of the original rational parameter. -/
theorem rational_function_algHom_polynomial_value (f : RatFunc K →ₐ[K] F) (p : Polynomial K) :
    f (algebraMap (Polynomial K) (RatFunc K) p) = Polynomial.aeval (f RatFunc.X) p := by
  have he : f.comp (IsScalarTower.toAlgHom K (Polynomial K) (RatFunc K)) =
      Polynomial.aeval (f RatFunc.X) := by
    apply Polynomial.algHom_ext
    simp only [AlgHom.comp_apply, Polynomial.aeval_X]
    rfl
  exact DFunLike.congr_fun he p

end DimensionFourDependence
