import DimensionFourDependence.BilinearLastDegreeObstructions
import DimensionFourDependence.PlanarNilpotentDependence

/-! # The principal-minor obstruction with one fixed last-variable output -/

namespace DimensionFourDependence

open MvPolynomial

universe u
set_option maxHeartbeats 2050000

variable {K : Type u} [Field K] [CharZero K]
local notation "R₃" => MvPolynomial (Fin 3) K
local notation "R₂" => MvPolynomial (Fin 2) K
local notation "P₂" => Polynomial R₂

theorem ternary_last_degree_zero_pderiv_last_eq_zero (u : R₃)
    (h : (ternaryLastVariableEquiv u).natDegree = 0) :
    pderiv (Fin.last 2) u = 0 := by
  apply ternaryLastVariableEquiv.injective
  rw [ternaryLastVariableEquiv_last_pderiv, map_zero]
  exact Polynomial.derivative_eq_zero.mpr h

/-- The exact reduced principal-minor equation is impossible when one
output is fixed in the last variable and the other moves. -/
theorem ternary_bilinear_minor_one_moving_output_impossible
    (u v : R₃) (i j : Fin 2) (hij : i ≠ j)
    (h0 : aeval (fun _ : Fin 3 => (0 : K)) u = 0) (hu0 : u ≠ 0)
    (hu : (ternaryLastVariableEquiv u).natDegree = 0)
    (hv : 0 < (ternaryLastVariableEquiv v).natDegree)
    (γ a : K) (hγ : γ ≠ 0)
    (h : pderiv j.castSucc u ^ 2 +
      pderiv i.castSucc u * (pderiv j.castSucc v + (C γ * v + C a) * pderiv (Fin.last 2) v) = 0) :
    False := by
  let e := ternaryLastVariableEquiv (K := K)
  have hud : pderiv (Fin.last 2) u = 0 := ternary_last_degree_zero_pderiv_last_eq_zero u hu
  have hui : pderiv i.castSucc u ≠ 0 := by
    intro hz
    have hSquare := h
    rw [hz, zero_mul, add_zero] at hSquare
    have hj : pderiv j.castSucc u = 0 := by
      by_contra hn
      exact pow_ne_zero 2 hn hSquare
    apply hu0
    apply normalized_polynomial_eq_zero_of_partials_zero u h0
    intro k
    refine Fin.lastCases hud (fun k => ?_) k
    by_cases hk : k = i
    · rwa [hk]
    · have he : k = j := by
        have hK := k.isLt
        have hI := i.isLt
        have hJ := j.isLt
        apply Fin.ext
        have hne (a b : Fin 2) (h : a ≠ b) : a.val ≠ b.val := fun hc => h (Fin.ext hc)
        have hn₁ := hne i j hij
        have hn₂ := hne k i hk
        omega
      rwa [he]
  let U := (e u).coeff 0
  have hU : e u = Polynomial.C U := Polynomial.eq_C_of_natDegree_eq_zero hu
  have hg (k : Fin 2) : e (pderiv k.castSucc u) = Polynomial.C (pderiv k U) := by
    change ternaryLastVariableEquiv (pderiv k.castSucc u) = _
    rw [ternaryLastVariableEquiv_active_pderiv]
    change ternaryCoefficientPartial k (e u) = _
    rw [hU, ternaryCoefficientPartial_C]
  have hU₀ : pderiv i U ≠ 0 := by
    intro hz
    apply hui
    apply e.injective
    rw [hg, hz, map_zero, map_zero]
  have hEval := congrArg e h
  change e (pderiv j.castSucc u ^ 2 +
    pderiv i.castSucc u * (pderiv j.castSucc v + (C γ * v + C a) * pderiv (Fin.last 2) v)) = e 0 at hEval
  simp only [map_add, map_mul, map_pow, map_zero, hg] at hEval
  have hc (k : K) : e (C k) = Polynomial.C (C k) := ternaryLastVariableEquiv_C k
  have hV (k : Fin 2) : e (pderiv k.castSucc v) = ternaryCoefficientPartial k (e v) :=
    ternaryLastVariableEquiv_active_pderiv k v
  have hV' : e (pderiv (Fin.last 2) v) = (e v).derivative := ternaryLastVariableEquiv_last_pderiv v
  rw [hV j, hV', hc γ, hc a] at hEval
  apply bilinear_one_moving_last_degree_minor_impossible (e v) hv (pderiv j U) (pderiv i U)
    hU₀ j γ a hγ
  rw [map_pow]
  linear_combination hEval

end DimensionFourDependence
