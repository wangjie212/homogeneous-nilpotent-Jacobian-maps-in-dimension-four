import DimensionFourDependence.GaussPencilDegreeBound
import DimensionFourDependence.NormalPlaneConstantIntersection

/-! # The source pencil base satisfies every normal coefficient equation

The exact reduced-pencil kernel makes the independent-parameter
normal/output pairing divisible by the pencil equation. At a base point
the entire pairing vanishes, including all coefficient equations.
A coefficient kernel of dimension at most one containing the fourth
axis has no other solutions, also after extending the ground field.
-/

namespace DimensionFourDependence

open MvPolynomial Matrix Module

set_option maxHeartbeats 2000000

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

/-- A one-dimensional coefficient kernel containing the fourth
axis has zero first three coordinates in every scalar extension. -/
theorem small_matrix_kernel_containing_fourth_axis
    {m : ℕ} (A : Matrix (Fin m) (Fin 4) K)
    (hdim : finrank K (LinearMap.ker A.toLin') ≤ 1)
    (haxis : A *ᵥ (Fin.snoc (0 : Fin 3 → K) 1 : Fin 4 → K) = 0)
    (x : Fin 4 → F) (hx : A.map (algebraMap K F) *ᵥ x = 0) :
    ∀ i : Fin 3, x i.castSucc = 0 := by
  obtain ⟨c, hc, hgen⟩ := matrix_kernel_finrank_le_one_constant_generator (E := F) A hdim
  let axis : Fin 4 → F := Fin.snoc (0 : Fin 3 → F) 1
  have haxisF : A.map (algebraMap K F) *ᵥ axis = 0 := by
    funext r
    have he := congrFun haxis r
    simp only [mulVec, dotProduct, Fin.sum_univ_castSucc, Fin.snoc_castSucc,
      Pi.zero_apply, mul_zero, Finset.sum_const_zero, Fin.snoc_last, mul_one, zero_add] at he
    simpa only [mulVec, dotProduct, Fin.sum_univ_castSucc, axis, Fin.snoc_castSucc,
      Pi.zero_apply, mul_zero, Finset.sum_const_zero, Fin.snoc_last, mul_one, zero_add,
      Matrix.map_apply, he, map_zero]
  obtain ⟨u, hu⟩ := hgen axis haxisF
  have hu0 : u ≠ 0 := by
    intro hz
    have he := congrFun hu (Fin.last 3)
    apply (one_ne_zero : (1 : F) ≠ 0)
    simpa only [axis, Fin.snoc_last, hz, zero_smul, Pi.zero_apply] using he
  have hcfirst (i : Fin 3) : algebraMap K F (c i.castSucc) = 0 := by
    have he := congrFun hu i.castSucc
    have hmul : u * algebraMap K F (c i.castSucc) = 0 := by
      simpa only [axis, Fin.snoc_castSucc, Pi.zero_apply, Pi.smul_apply, smul_eq_mul] using he.symm
    exact (mul_eq_zero.mp hmul).resolve_left hu0
  obtain ⟨v, hv⟩ := hgen x hx
  intro i
  simpa only [Pi.smul_apply, smul_eq_mul, hcfirst i, mul_zero] using congrFun hv i.castSucc

/-- Every actual base point of a reduced source pencil satisfies
the polynomial coefficient equations of a normal/output relation. -/
theorem pencil_base_output_mem_normal_coefficient_kernel
    (p q : MvPolynomial (Fin 4) K) (hq : q ≠ 0) (hrel : IsRelPrime p q)
    (H : Fin 4 → MvPolynomial (Fin 4) K) (v : Fin 4 → Polynomial K)
    (hsection : (∑ i, Polynomial.aeval
      (algebraMap (MvPolynomial (Fin 4) K) (FractionRing (MvPolynomial (Fin 4) K)) p /
        algebraMap (MvPolynomial (Fin 4) K) (FractionRing (MvPolynomial (Fin 4) K)) q)
      (v i) * algebraMap (MvPolynomial (Fin 4) K) (FractionRing (MvPolynomial (Fin 4) K)) (H i)) = 0)
    (ψ : MvPolynomial (Fin 4) K →ₐ[K] F) (hpψ : ψ p = 0) (hqψ : ψ q = 0) :
    (polynomialCovectorCoefficientMatrix v).map (algebraMap K F) *ᵥ (fun i => ψ (H i)) = 0 := by
  have hdiv : sourcePencilEquation p q ∣ parametricOutputPairing v H :=
    (sourcePencilEquation_dvd_iff_eval_fraction_zero p q hq hrel _).mpr
      ((parametricOutputPairing_eval_fraction v H _).trans hsection)
  obtain ⟨Q, hQ⟩ := hdiv
  have hmap := congrArg (Polynomial.map ψ.toRingHom) hQ
  have hL : Polynomial.map ψ.toRingHom (sourcePencilEquation p q) = 0 := by
    simp [sourcePencilEquation, hpψ, hqψ]
  rw [Polynomial.map_mul, hL, zero_mul] at hmap
  have hcomp : ψ.toRingHom.comp (MvPolynomial.C : K →+* MvPolynomial (Fin 4) K) =
      algebraMap K F := by
    ext a
    exact ψ.commutes a
  apply polynomial_covector_relation_mem_extended_coefficient_kernel v
  change (∑ i, Polynomial.C (ψ.toRingHom (H i)) *
    Polynomial.map (algebraMap K F) (v i)) = 0
  simpa only [parametricOutputPairing, Polynomial.map_sum, Polynomial.map_mul,
    Polynomial.map_map, hcomp, Polynomial.map_C, mul_comm] using hmap

/-- Independent normal jets and the fixed fourth-axis normal
coordinate force every actual pencil-base output onto that axis. -/
theorem pencil_base_output_first_three_zero_of_normal_jets
    (p q : MvPolynomial (Fin 4) K) (hq : q ≠ 0) (hrel : IsRelPrime p q)
    (H : Fin 4 → MvPolynomial (Fin 4) K)
    (w : Fin 4 → RatFunc K) (v : Fin 4 → Polynomial K) (r : RatFunc K)
    (hLI : LinearIndependent (RatFunc K) (rationalParameterJetMatrix w).row)
    (hrep : ∀ i, w i = r * algebraMap (Polynomial K) (RatFunc K) (v i))
    (hvlast : v (Fin.last 3) = 0)
    (hsection : (∑ i, Polynomial.aeval
      (algebraMap (MvPolynomial (Fin 4) K) (FractionRing (MvPolynomial (Fin 4) K)) p /
        algebraMap (MvPolynomial (Fin 4) K) (FractionRing (MvPolynomial (Fin 4) K)) q)
      (v i) * algebraMap (MvPolynomial (Fin 4) K) (FractionRing (MvPolynomial (Fin 4) K)) (H i)) = 0)
    (ψ : MvPolynomial (Fin 4) K →ₐ[K] F) (hpψ : ψ p = 0) (hqψ : ψ q = 0) :
    ∀ i : Fin 3, ψ (H i.castSucc) = 0 := by
  apply small_matrix_kernel_containing_fourth_axis
    (polynomialCovectorCoefficientMatrix v)
    (polynomial_normal_coefficient_kernel_finrank_le_one w v r hLI hrep)
    ?_ (fun i => ψ (H i))
    (pencil_base_output_mem_normal_coefficient_kernel p q hq hrel H v hsection ψ hpψ hqψ)
  funext j
  simp only [mulVec, dotProduct, Fin.sum_univ_castSucc, Fin.snoc_castSucc,
    Pi.zero_apply, mul_zero, Finset.sum_const_zero, Fin.snoc_last, mul_one, zero_add,
    polynomialCovectorCoefficientMatrix, hvlast, Polynomial.coeff_zero]

end DimensionFourDependence
