import DimensionFourDependence.GenericReducedHomogeneousPencil
import DimensionFourDependence.RectangularJacobianRank

/-! # A positive reduced homogeneous source pencil has two independent gradients -/

namespace DimensionFourDependence

open MvPolynomial Matrix

universe u
set_option maxHeartbeats 2500000

variable {K : Type u} [Field K] [CharZero K]
local notation "R₀" => MvPolynomial (Fin 4) K
local notation "F₀" => FractionRing (MvPolynomial (Fin 4) K)

/-- The two actual homogeneous source pencil gradients are independent
over the original rational source field. Euler contraction and the
constructed nonzero Wronskian exclude every rational relation. -/
theorem positive_reduced_homogeneous_source_pencil_gradients_independent
    (p q : R₀) {D : ℕ} (hD : 0 < D) (hp : p ≠ 0) (hq : q ≠ 0)
    (hpH : p.IsHomogeneous D) (hqH : q.IsHomogeneous D) (hrel : IsRelPrime p q) :
    LinearIndependent F₀ ![(fun i => algebraMap R₀ F₀ (pderiv i p)),
      (fun i => algebraMap R₀ F₀ (pderiv i q))] := by
  let f := algebraMap R₀ F₀
  let gp : Fin 4 → F₀ := fun i => f (pderiv i p)
  let gq : Fin 4 → F₀ := fun i => f (pderiv i q)
  have hEuler (r : R₀) (hr : r.IsHomogeneous D) :
      (∑ i, rationalCoordinate (K := K) i * f (pderiv i r)) = (D : F₀) * f r := by
    have he := congrArg f hr.sum_X_mul_pderiv
    simpa only [rationalCoordinate, map_sum, map_mul, nsmul_eq_mul, map_natCast] using he
  have hDn : (D : F₀) ≠ 0 := Nat.cast_ne_zero.mpr hD.ne'
  have hqF : f q ≠ 0 := fun hz => hq (IsFractionRing.injective R₀ F₀ (hz.trans (map_zero _).symm))
  obtain ⟨i, hW⟩ := positive_homogeneous_reduced_pencil_has_nonzero_wronskian p q hD hp hpH hrel
  rw [LinearIndependent.pair_iff]
  intro a b hab
  have hgr (j : Fin 4) : a * gp j + b * gq j = 0 := congrFun hab j
  have hsum : (∑ j, rationalCoordinate (K := K) j * (a * gp j + b * gq j)) = 0 := by
    simp only [hgr, mul_zero, Finset.sum_const_zero]
  have hpull (c : F₀) (v : Fin 4 → F₀) :
      (∑ j, rationalCoordinate (K := K) j * (c * v j)) =
      c * ∑ j, rationalCoordinate (K := K) j * v j := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    ring
  simp only [mul_add, Finset.sum_add_distrib, hpull] at hsum
  rw [hEuler p hpH, hEuler q hqH] at hsum
  have hscalar : a * f p + b * f q = 0 := by
    apply (mul_eq_zero.mp (show (D : F₀) * (a * f p + b * f q) = 0 by linear_combination hsum)).resolve_left hDn
  by_cases ha : a = 0
  · refine ⟨ha, ?_⟩
    rw [ha, zero_mul, zero_add] at hscalar
    exact (mul_eq_zero.mp hscalar).resolve_right hqF
  · exfalso
    have hWF : f (q * pderiv i p - p * pderiv i q) ≠ 0 :=
      fun hz => hW (IsFractionRing.injective R₀ F₀ (hz.trans (map_zero _).symm))
    apply mul_ne_zero ha hWF
    simp only [map_sub, map_mul]
    change a * (f q * gp i - f p * gq i) = 0
    linear_combination f q * hgr i - gq i * hscalar

end DimensionFourDependence
