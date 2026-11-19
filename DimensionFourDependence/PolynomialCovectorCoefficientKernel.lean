import DimensionFourDependence.GaussNormalConstantSpan
import DimensionFourDependence.RulingFormCoordinateSpan

/-! # Polynomial moving-plane incidence gives the actual constant coefficient kernel -/

namespace DimensionFourDependence

open Matrix Module

variable {K : Type*} [Field K] {n : ℕ}

/-- A finite bound containing every coefficient of the original
polynomial plane covector. -/
noncomputable def polynomialCovectorCoefficientBound (v : Fin n → Polynomial K) : ℕ :=
  Finset.univ.sup (fun i => (v i).natDegree) + 1

/-- The actual original-field coefficient equations of a moving
polynomial plane, without selecting a finite subfamily of parameter values. -/
noncomputable def polynomialCovectorCoefficientMatrix (v : Fin n → Polynomial K) :
    Matrix (Fin (polynomialCovectorCoefficientBound v)) (Fin n) K :=
  fun j i => (v i).coeff j.val

/-- The finite coefficient matrix expresses exactly the polynomial
identity that a constant point lies in every plane of the family. -/
theorem polynomial_covector_coefficient_kernel_iff
    (v : Fin n → Polynomial K) (x : Fin n → K) :
    polynomialCovectorCoefficientMatrix v *ᵥ x = 0 ↔
      (∑ i, Polynomial.C (x i) * v i) = 0 := by
  constructor
  · intro hx
    apply Polynomial.ext
    intro j
    by_cases hj : j < polynomialCovectorCoefficientBound v
    · have hr := congrFun hx ⟨j, hj⟩
      simpa only [polynomialCovectorCoefficientMatrix, Matrix.mulVec, dotProduct,
        Pi.zero_apply, Polynomial.finsetSum_coeff, Polynomial.coeff_C_mul, Polynomial.coeff_mul_C,
        Polynomial.coeff_zero, mul_comm] using hr
    · simp only [Polynomial.finsetSum_coeff, Polynomial.coeff_C_mul, Polynomial.coeff_zero]
      apply Finset.sum_eq_zero
      intro i hi
      have hbound : (v i).natDegree ≤ Finset.univ.sup (fun a => (v a).natDegree) :=
        Finset.le_sup (f := fun a : Fin n => (v a).natDegree) (Finset.mem_univ i)
      have hlarge : (v i).natDegree < j := by
        dsimp only [polynomialCovectorCoefficientBound] at hj
        omega
      rw [Polynomial.coeff_eq_zero_of_natDegree_lt hlarge, mul_zero]
  · intro hp
    funext j
    have hc := congrArg (fun p : Polynomial K => p.coeff j.val) hp
    simpa only [polynomialCovectorCoefficientMatrix, Matrix.mulVec, dotProduct,
      Pi.zero_apply, Polynomial.finsetSum_coeff, Polynomial.coeff_C_mul, Polynomial.coeff_mul_C,
      Polynomial.coeff_zero, mul_comm] using hc

variable {E : Type*} [Field E] [Algebra K E]

/-- A polynomial plane identity over an extension field gives all
the original finite coefficient equations over that same field. -/
theorem polynomial_covector_relation_mem_extended_coefficient_kernel
    (v : Fin n → Polynomial K) (x : Fin n → E)
    (hpoly : (∑ i, Polynomial.C (x i) * Polynomial.map (algebraMap K E) (v i)) = 0) :
    (polynomialCovectorCoefficientMatrix v).map (algebraMap K E) *ᵥ x = 0 := by
  funext j
  have hc := congrArg (fun p : Polynomial E => p.coeff j.val) hpoly
  simpa only [polynomialCovectorCoefficientMatrix, Matrix.mulVec, dotProduct, Matrix.map_apply,
    Pi.zero_apply, Polynomial.finsetSum_coeff, Polynomial.coeff_C_mul, Polynomial.coeff_mul_C, Polynomial.coeff_map,
    Polynomial.coeff_zero, mul_comm] using hc

variable {L : Type*} [Field L] [Algebra K L] [Algebra E L] [IsScalarTower K E L]

/-- At a parameter transcendental over the point's coordinate
field, moving-plane incidence forces the entire polynomial incidence
identity over that field. -/
theorem transcendental_parameter_plane_incidence_polynomial_identity
    (v : Fin n → Polynomial K) (x : Fin n → E) (t : L) (ht : Transcendental E t)
    (hplane : ∑ i, algebraMap E L (x i) * Polynomial.aeval t (v i) = 0) :
    (∑ i, Polynomial.C (x i) * Polynomial.map (algebraMap K E) (v i)) = 0 := by
  apply transcendental_iff.mp ht
  have hmaps : (algebraMap E L).comp (algebraMap K E) = algebraMap K L := by
    ext c
    exact (IsScalarTower.algebraMap_apply K E L c).symm
  have hmap (p : Polynomial K) : Polynomial.aeval t (p.map (algebraMap K E)) = Polynomial.aeval t p :=
    (Polynomial.aeval_eq_aeval_map hmaps p t).symm
  simpa only [map_sum, map_mul, Polynomial.aeval_C, hmap] using hplane

/-- The actual finite constant coefficient kernel contains every
point incident to the family at a parameter transcendental over its
coordinate field. No incidence at other parameter values is assumed. -/
theorem transcendental_parameter_plane_incidence_mem_coefficient_kernel
    (v : Fin n → Polynomial K) (x : Fin n → E) (t : L) (ht : Transcendental E t)
    (hplane : ∑ i, algebraMap E L (x i) * Polynomial.aeval t (v i) = 0) :
    (polynomialCovectorCoefficientMatrix v).map (algebraMap K E) *ᵥ x = 0 :=
  polynomial_covector_relation_mem_extended_coefficient_kernel v x
    (transcendental_parameter_plane_incidence_polynomial_identity v x t ht hplane)

end DimensionFourDependence
