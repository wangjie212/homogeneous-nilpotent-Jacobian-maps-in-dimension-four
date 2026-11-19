import DimensionFourDependence.TernaryPlanarSpecialization
import DimensionFourDependence.ConstantKernelSourceReduction
import DimensionFourDependence.PlanarNilpotentDependence
import DimensionFourDependence.LinearConjugacyEvaluationExtension

/-! # A constant right kernel reduces the nonhomogeneous ternary problem to the plane -/

namespace DimensionFourDependence

open MvPolynomial Matrix

universe u
set_option maxHeartbeats 2000000

variable {K : Type u} [Field K] [CharZero K]
local notation "R₃" => MvPolynomial (Fin 3) K
local notation "R₂" => MvPolynomial (Fin 2) K

/-- A nonzero original constant right-kernel vector forces a constant
relation among the outputs of a normalized ternary nilpotent map. -/
theorem normalized_ternary_nilpotent_constant_right_kernel_componentsDependent
    (H : Fin 3 → R₃) (h0 : ∀ i, aeval (fun _ : Fin 3 => (0 : K)) (H i) = 0)
    (hN : IsNilpotent (jac H)) (c : Fin 3 → K) (hc : c ≠ 0)
    (hker : jac H *ᵥ (fun i => C (c i)) = 0) :
    ComponentsDependent H := by
  by_contra hind
  obtain ⟨T, S, hTS, hST, hp⟩ :=
    constant_right_kernel_constructs_coordinate_partial_zero H c hc hker (Fin.last 2)
  let G := linearPolynomialConjugate T S H
  have hGi := linearPolynomialConjugate_componentsIndependent T S hTS hST H hind
  have hGn := linearPolynomialConjugate_nilpotent T S hTS hST H hN
  have hG0 (i : Fin 3) : aeval (fun _ : Fin 3 => (0 : K)) (G i) = 0 := by
    have he := linearPolynomialConjugate_aeval_extension_eq_zero T S hTS H
      (fun _ : Fin 3 => (0 : K)) h0
    have hz : S.map (algebraMap K K) *ᵥ (fun _ : Fin 3 => (0 : K)) = 0 := mulVec_zero _
    rw [hz] at he
    exact he i
  let r : R₂ →ₐ[K] R₃ := rename Fin.castSucc
  have hsmall (i : Fin 2) : ∃ P : R₂, r P = G i.castSucc :=
    zero_last_partial_constructs_smaller_source_polynomial (G i.castSucc) (hp i.castSucc)
  choose B hB using hsmall
  have hBlock := leading_block_isNilpotent_of_last_column_zero (jac G) hGn hp
  have hMat : (jac B).map r = (jac G).submatrix Fin.castSucc Fin.castSucc := by
    funext i j
    change r (pderiv j (B i)) = pderiv j.castSucc (G i.castSucc)
    rw [← hB i]
    exact (pderiv_rename (Fin.castSucc_injective 2) j (B i)).symm
  have hBn : IsNilpotent (jac B) := by
    obtain ⟨k, hk⟩ := hBlock
    refine ⟨k, ?_⟩
    apply Matrix.map_injective (rename_injective Fin.castSucc (Fin.castSucc_injective 2))
    change ((jac B) ^ k).map r.toRingHom = _
    rw [Matrix.map_pow]
    change ((jac B).map r) ^ k = _
    rw [hMat, hk]
    rfl
  have hB0 (i : Fin 2) : aeval (fun _ : Fin 2 => (0 : K)) (B i) = 0 := by
    have he := hG0 i.castSucc
    rw [← hB i] at he
    change aeval (fun _ : Fin 3 => (0 : K)) (rename Fin.castSucc (B i)) = 0 at he
    rwa [aeval_rename] at he
  obtain ⟨a, ha, hrel⟩ := normalized_planar_nilpotent_componentsDependent B hB0 hBn
  let b : Fin 3 → K := Fin.snoc a 0
  have hb : b ≠ 0 := by
    intro hz
    apply ha
    funext i
    have hi := congrFun hz i.castSucc
    simpa only [b, Fin.snoc_castSucc, Pi.zero_apply] using hi
  apply hGi
  refine ⟨b, hb, ?_⟩
  have he := congrArg r hrel
  change r (∑ i, a i • B i) = r 0 at he
  have hr (c : K) : r (C c) = C c := r.commutes c
  simp only [map_sum, smul_eq_C_mul, map_mul, hr, hB, map_zero] at he
  rw [Fin.sum_univ_castSucc]
  simpa only [b, Fin.snoc_castSucc, Fin.snoc_last, zero_smul, add_zero, zero_add,
    smul_eq_C_mul] using he

end DimensionFourDependence
