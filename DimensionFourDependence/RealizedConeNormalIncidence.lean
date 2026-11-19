import DimensionFourDependence.MatrixRankFieldMap
import DimensionFourDependence.AffineConeVertexDifferential
import DimensionFourDependence.TranscendentalSeparatingDerivation
import DimensionFourDependence.GaussRulingIncidence

/-! # The actual normalized image normal kills projected fiber directions

Nilpotence and rank three persist through a source-field embedding.
The kernel-image inclusion therefore pairs the realized image normal
with every realized kernel vector. A separating derivation constructs
the tangent of an affine-linear projected generic fiber. The zero
fourth normal entry removes its unrestricted fourth tangent coordinate.
-/

namespace DimensionFourDependence

open MvPolynomial Matrix

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 100000

variable {K E G : Type*} [Field K] [Field E] [Field G]
    [Algebra K E] [Algebra E G] [Algebra K G] [IsScalarTower K E G]

local notation "S₀" => FractionRing (MvPolynomial (Fin 4) K)

/-- The normalized original image normal annihilates every right-kernel
vector after any actual source-field embedding. Rank and nilpotence in
the target field are conclusions of their original polynomial versions. -/
theorem realized_nilpotent_image_normal_kernel_pairing
    (H : Fin 4 → MvPolynomial (Fin 4) K) (hN : IsNilpotent (jac H))
    (hrank : polyRank (jac H) = 3) (I : ImageRelationWitness H)
    (f : S₀ →ₐ[K] G) (u : Fin 4 → G)
    (hu : ((jac H).map (algebraMap (MvPolynomial (Fin 4) K) S₀)).map f.toRingHom *ᵥ u = 0) :
    (fun i => f (rationalImageNormal H I.equation i /
      rationalImageNormal H I.equation (imageNormalPivot H I))) ⬝ᵥ u = 0 := by
  let N₀ := (jac H).map (algebraMap (MvPolynomial (Fin 4) K) S₀)
  let N := N₀.map f.toRingHom
  have hn : IsNilpotent N :=
    (hN.map (algebraMap (MvPolynomial (Fin 4) K) S₀).mapMatrix).map f.toRingHom.mapMatrix
  have hr : N.rank + 1 = 4 := by
    rw [show N = N₀.map f.toRingHom from rfl, matrix_rank_field_map]
    change polyRank (jac H) + 1 = 4
    omega
  have hleft : (fun i => f (rationalImageNormal H I.equation i)) ᵥ* N = 0 := by
    funext j
    change (∑ i, f (rationalImageNormal H I.equation i) *
      f (algebraMap (MvPolynomial (Fin 4) K) S₀ (jac H i j))) = 0
    have he := congrArg f (congrFun
      (imageRelationNormal_rational_left_kernel H I.equation I.vanishing) j)
    simpa only [rationalImageNormal, vecMul, dotProduct, Matrix.map_apply,
      Pi.zero_apply, map_sum, map_mul, map_zero] using he
  have he := matrix_nilpotent_kernel_dot_zero N hn (by norm_num) hr
    (fun i => f (rationalImageNormal H I.equation i)) u hleft hu
  simp only [dotProduct] at he
  simp only [map_div₀, dotProduct, div_mul_eq_mul_div, ← Finset.sum_div]
  rw [he, zero_div]

variable [CharZero K]

/-- On an actual constant-output fiber with affine-linear first three
coordinates, the specified fourth-axis vertex constructs the projected
normal-direction incidence. No tangent derivation or kernel identity is
assumed, and no condition on the fourth source coordinate is needed. -/
theorem realized_fixed_vertex_normal_incident_projected_fiber_direction
    (H : Fin 4 → MvPolynomial (Fin 4) K) (hN : IsNilpotent (jac H))
    (hrank : polyRank (jac H) = 3) (I : ImageRelationWitness H)
    (hvertex : rationalImageNormal H I.equation (Fin.last 3) = 0)
    (f : S₀ →ₐ[K] G) (z : Fin 4 → G)
    (hf : ∀ i, f (rationalCoordinate (K := K) i) = z i)
    (y : Fin 4 → E) (hout : ∀ i, aeval z (H i) = algebraMap E G (y i))
    (ν : Fin 3 → E)
    (hν : ∀ i, algebraMap E G (ν i) = f (rationalImageNormal H I.equation i.castSucc /
      rationalImageNormal H I.equation (imageNormalPivot H I)))
    (t : G) (ht : Transcendental E t) (x A : Fin 3 → E)
    (hx : ∀ i, z i.castSucc = algebraMap E G (x i) + algebraMap E G (A i) * t) :
    (∑ i : Fin 3, ν i * A i) = 0 := by
  let : CharZero E := charZero_of_injective_algebraMap (algebraMap K E).injective
  obtain ⟨D, hD⟩ := exists_derivation_apply_eq_one_of_transcendental t ht
  have heval (Q : MvPolynomial (Fin 4) K) :
      f (algebraMap (MvPolynomial (Fin 4) K) S₀ Q) = aeval z Q := by
    have he := comp_aeval_apply (rationalCoordinate (K := K) (n := 4)) f Q
    rw [rationalCoordinate_aeval] at he
    simpa only [hf] using he
  have hkernel : ((jac H).map (algebraMap (MvPolynomial (Fin 4) K) S₀)).map f.toRingHom *ᵥ
      (fun i => D (z i)) = 0 := by
    funext i
    have he := derivation_multivariate_aeval_chain_rule (D.restrictScalars K) z (H i)
    rw [hout] at he
    have hzero : (D.restrictScalars K) (algebraMap E G (y i)) = 0 := D.map_algebraMap _
    rw [hzero] at he
    simpa only [mulVec, dotProduct, Matrix.map_apply, jac, Matrix.of_apply,
      AlgHom.toRingHom_eq_coe, RingHom.coe_coe, heval,
      Derivation.restrictScalars_apply, Pi.zero_apply] using he.symm
  have hpair := realized_nilpotent_image_normal_kernel_pairing H hN hrank I f
    (fun i => D (z i)) hkernel
  have hDz (i : Fin 3) : D (z i.castSucc) = algebraMap E G (A i) := by
    rw [hx]
    simp [D.leibniz, hD, smul_eq_mul]
  have hlast : f (rationalImageNormal H I.equation (Fin.last 3) /
      rationalImageNormal H I.equation (imageNormalPivot H I)) = 0 := by
    rw [hvertex, zero_div, map_zero]
  have hsmall : ∑ i : Fin 3, algebraMap E G (ν i) * algebraMap E G (A i) = 0 := by
    simpa only [dotProduct, Fin.sum_univ_castSucc, hlast, zero_mul, add_zero, hDz, ← hν] using hpair
  apply (algebraMap E G).injective
  simpa only [map_sum, map_mul, map_zero] using hsmall

end DimensionFourDependence
