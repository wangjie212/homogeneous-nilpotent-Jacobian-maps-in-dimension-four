import DimensionFourDependence.AffineTriangularDivisibility
import DimensionFourDependence.AffineQuadraticShearInvariants
import DimensionFourDependence.PolynomialParameterTraceSpecialization

/-! # The polynomial trace constructs an actual binary quadratic potential -/

namespace DimensionFourDependence

open MvPolynomial Matrix

universe u
set_option maxHeartbeats 3200000

variable {K : Type u} [Field K] [CharZero K]
local notation "R₃" => MvPolynomial (Fin 3) K
local notation "R₂" => MvPolynomial (Fin 2) K

/-- Two linearly independent ordinary polynomials have evaluation rows
with nonzero determinant at two original scalar parameters. -/
theorem independent_polynomials_construct_invertible_evaluation_pair
    (p q : Polynomial K)
    (hind : ∀ a b : K, Polynomial.C a * p + Polynomial.C b * q = 0 → a = 0 ∧ b = 0) :
    ∃ t u : K, p.eval t * q.eval u - q.eval t * p.eval u ≠ 0 := by
  have hp : ∃ t : K, p.eval t ≠ 0 := by
    by_contra! h
    have hz : p = 0 := Polynomial.eq_zero_of_infinite_isRoot p
      (Set.infinite_univ.mono (fun t _ => h t))
    exact one_ne_zero ((hind 1 0 (by simp [hz])).1)
  obtain ⟨t, ht⟩ := hp
  by_contra! h
  have he : Polynomial.C (-(q.eval t)) * p + Polynomial.C (p.eval t) * q = 0 := by
    apply Polynomial.eq_zero_of_infinite_isRoot
    apply Set.infinite_univ.mono
    intro u _
    change (_ + _ : Polynomial K).eval u = 0
    simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C]
    linear_combination h t u
  exact ht (hind _ _ he).2

/-- A polynomial trace with common parameter and affine vertical
output specializes to a whole affine tangent equation at each scalar
level. Coordinates are ordered with the vertical variable last. -/
theorem ternary_vertical_parameter_trace_specializes_affine_tangent
    (r : R₃) (hr : pderiv 2 r ≠ 0) (f g a b c : Polynomial K)
    (ht : Polynomial.aeval r f.derivative * pderiv 0 r +
      Polynomial.aeval r g.derivative * pderiv 1 r +
      (Polynomial.aeval r c.derivative + Polynomial.aeval r b.derivative * X 0 +
        Polynomial.aeval r a.derivative * X 1) * pderiv 2 r = 0) (t : K) :
    affineProjectedTangentAction ![f.derivative.eval t, g.derivative.eval t]
      ![c.derivative.eval t, b.derivative.eval t, a.derivative.eval t] r = 0 := by
  let p := r - C t
  have hp : p ≠ 0 := by
    intro h
    apply hr
    have hd := congrArg (pderiv (R := K) (2 : Fin 3)) h
    change pderiv 2 (r - C t) = pderiv 2 (0 : R₃) at hd
    simpa only [map_sub, map_zero, pderiv_C, sub_zero] using hd
  apply affine_triangular_level_tangency_forces_global_annihilation _ _ r t hp
  let D := fun A : Polynomial K => Polynomial.aeval r A.derivative - C (A.derivative.eval t)
  have hd (A : Polynomial K) : p ∣ D A :=
    polynomial_parameter_level_dvd_evaluation_difference r A.derivative t
  have hsum : p ∣ D f * pderiv 0 r + D g * pderiv 1 r +
      (D c + D b * X 0 + D a * X 1) * pderiv 2 r :=
    dvd_add (dvd_add (dvd_mul_of_dvd_left (hd f) _) (dvd_mul_of_dvd_left (hd g) _))
      (dvd_mul_of_dvd_left (dvd_add (dvd_add (hd c) (dvd_mul_of_dvd_left (hd b) _))
        (dvd_mul_of_dvd_left (hd a) _)) _)
  have he : D f * pderiv 0 r + D g * pderiv 1 r +
      (D c + D b * X 0 + D a * X 1) * pderiv 2 r =
      -affineProjectedTangentAction ![f.derivative.eval t, g.derivative.eval t]
        ![c.derivative.eval t, b.derivative.eval t, a.derivative.eval t] r := by
    change _ = -(C (f.derivative.eval t) * pderiv 0 r + C (g.derivative.eval t) * pderiv 1 r +
      (C (c.derivative.eval t) + C (b.derivative.eval t) * X 0 + C (a.derivative.eval t) * X 1) * pderiv 2 r)
    dsimp only [D]
    linear_combination ht
  rw [he] at hsum
  exact dvd_neg.mp hsum

/-- The actual two independent horizontal tangent directions yield
a quadratic potential and a univariate composite parameter. The
potential has zero constant coefficient. -/
theorem ternary_vertical_parameter_has_quadratic_potential
    (r : R₃) (hr : pderiv 2 r ≠ 0) (f g a b c : Polynomial K)
    (hind : ∀ u v : K, Polynomial.C u * f.derivative + Polynomial.C v * g.derivative = 0 →
      u = 0 ∧ v = 0)
    (ht : Polynomial.aeval r f.derivative * pderiv 0 r +
      Polynomial.aeval r g.derivative * pderiv 1 r +
      (Polynomial.aeval r c.derivative + Polynomial.aeval r b.derivative * X 0 +
        Polynomial.aeval r a.derivative * X 1) * pderiv 2 r = 0) :
    ∃ (l m : Fin 3 → K) (T : Polynomial K), l 2 = m 1 ∧
      r = Polynomial.aeval (X 2 - rename Fin.castSucc (affineTangentQuadraticPotential l m)) T := by
  let u (t : K) : Fin 2 → K := ![f.derivative.eval t, g.derivative.eval t]
  let b₀ (t : K) : Fin 3 → K := ![c.derivative.eval t, b.derivative.eval t, a.derivative.eval t]
  have htan (t : K) : affineProjectedTangentAction (u t) (b₀ t) r = 0 :=
    ternary_vertical_parameter_trace_specializes_affine_tangent r hr f g a b c ht t
  obtain ⟨t, τ, hdet⟩ := independent_polynomials_construct_invertible_evaluation_pair f.derivative g.derivative hind
  obtain ⟨l, m, hl, hm⟩ := independent_projected_affine_tangents_construct_normalized_lifts
    r (u t) (u τ) hdet (b₀ t) (b₀ τ) (htan t) (htan τ)
  have hclosed := invariant_affine_tangent_lifts_closed r hr l m hl hm
  let Q := affineTangentQuadraticPotential l m
  have hx : rename Fin.castSucc (pderiv (0 : Fin 2) Q) = affineTangentVerticalCoefficient l := by
    change rename Fin.castSucc (pderiv (0 : Fin 2) (affineTangentQuadraticPotential l m)) = _
    rw [affineTangentQuadraticPotential_pderiv_x]
    simp only [map_add, map_mul, rename_C, rename_X]
    rfl
  have hy : rename Fin.castSucc (pderiv (1 : Fin 2) Q) = affineTangentVerticalCoefficient m := by
    change rename Fin.castSucc (pderiv (1 : Fin 2) (affineTangentQuadraticPotential l m)) = _
    rw [affineTangentQuadraticPotential_pderiv_z l m hclosed]
    simp only [map_add, map_mul, rename_C, rename_X]
    rfl
  obtain ⟨T, hT⟩ := quadratic_gradient_lifts_invariant_polynomial_in_graph Q r
    (by rw [hx, ← affineTangentLiftX_apply]; exact hl)
    (by rw [hy, ← affineTangentLiftZ_apply]; exact hm)
  exact ⟨l, m, T, hclosed, hT⟩

end DimensionFourDependence
