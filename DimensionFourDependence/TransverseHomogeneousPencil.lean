import DimensionFourDependence.VertexIndependentReducedDenominator
import DimensionFourDependence.HomogeneousAffineLeadingCoefficient
import DimensionFourDependence.TranscendentalPolynomialParametrization
import DimensionFourDependence.CoprimeTernaryProjectiveBase

/-! # A transverse homogeneous pencil constant on a fiber has constant projective direction -/

namespace DimensionFourDependence

open MvPolynomial

set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 100000

universe u

variable {K : Type u} [Field K]

/-- Two original vertex-independent homogeneous pencil members
descend together to coprime homogeneous ternary polynomials, with
their exact original polynomial values retained. -/
theorem vertex_independent_coprime_pencil_constructs_ternary_pair
    (p q : MvPolynomial (Fin 4) K) (hp : p ≠ 0) (hq : q ≠ 0) (hrel : IsRelPrime p q)
    {D : ℕ} (hpH : p.IsHomogeneous D) (hqH : q.IsHomogeneous D)
    (hpw : p.degreeOf (Fin.last 3) = 0) (hqw : q.degreeOf (Fin.last 3) = 0) :
    ∃ p₀ q₀ : MvPolynomial (Fin 3) K, p₀ ≠ 0 ∧ q₀ ≠ 0 ∧ IsRelPrime p₀ q₀ ∧
      p₀.IsHomogeneous D ∧ q₀.IsHomogeneous D ∧ rename Fin.castSucc p₀ = p ∧ rename Fin.castSucc q₀ = q := by
  obtain ⟨p₀, hp₀⟩ := vertex_degree_zero_constructs_transverse_polynomial p hpw
  obtain ⟨q₀, hq₀⟩ := vertex_degree_zero_constructs_transverse_polynomial q hqw
  let ρ : Fin 4 → Fin 3 := Fin.lastCases 0 (fun i => i)
  have hback (R : MvPolynomial (Fin 3) K) : rename ρ (rename Fin.castSucc R) = R := by
    rw [rename_rename]
    have hfun : ρ ∘ Fin.castSucc = id := by funext i; simp [ρ]
    rw [hfun, rename_id]
    rfl
  have hp₀0 : p₀ ≠ 0 := by intro hz; apply hp; rw [← hp₀, hz, map_zero]
  have hq₀0 : q₀ ≠ 0 := by intro hz; apply hq; rw [← hq₀, hz, map_zero]
  have hrel₀ : IsRelPrime p₀ q₀ := by
    intro R hRp hRq
    have hu : IsUnit (rename Fin.castSucc R : MvPolynomial (Fin 4) K) := hrel
      (by rw [← hp₀]; exact map_dvd (rename Fin.castSucc) hRp)
      (by rw [← hq₀]; exact map_dvd (rename Fin.castSucc) hRq)
    simpa only [hback] using hu.map (rename ρ)
  have hp₀H : p₀.IsHomogeneous D := by
    have he : (rename ρ p).IsHomogeneous D := hpH.rename_isHomogeneous
    rwa [← hp₀, hback] at he
  have hq₀H : q₀.IsHomogeneous D := by
    have he : (rename ρ q).IsHomogeneous D := hqH.rename_isHomogeneous
    rwa [← hq₀, hback] at he
  exact ⟨p₀, q₀, hp₀0, hq₀0, hrel₀, hp₀H, hq₀H, hp₀, hq₀⟩

variable {E G : Type u} [Field E] [Field G] [Algebra K E] [Algebra E G] [Algebra K G]
    [IsScalarTower K E G]

/-- A positive-degree original homogeneous invariant constant on
an actual affine line vanishes at that line's original direction. -/
theorem homogeneous_invariant_constant_on_actual_affine_line_direction_zero
    {n D : ℕ} (P : MvPolynomial (Fin n) K) (hD : 0 < D) (hP : P.IsHomogeneous D)
    (t : G) (ht : Transcendental E t) (z : Fin n → G) (x A : Fin n → E)
    (hx : ∀ i, z i = algebraMap E G (x i) + algebraMap E G (A i) * t)
    (c : E) (hc : aeval z P = algebraMap E G c) : aeval A P = 0 := by
  let s : Fin n → Polynomial E := fun i => Polynomial.C (x i) + Polynomial.C (A i) * Polynomial.X
  have hs (i : Fin n) : Polynomial.aeval t (s i) = z i := by simpa [s] using (hx i).symm
  have he := original_polynomial_parametrization_constant_of_transcendental t ht z s hs P c hc
  have hcoeff := congrArg (fun Q : Polynomial E => Q.coeff D) he
  rw [homogeneous_affine_line_coefficient_at_degree P hP x A] at hcoeff
  simpa only [Polynomial.coeff_C_of_ne_zero (by omega : D ≠ 0)] using hcoeff

variable [CharZero K]

/-- A vertex-independent reduced homogeneous pencil constant on
an actual fiber forces every projected direction ratio algebraic over
the original field. Both original polynomial members are used. -/
theorem transverse_coprime_pencil_constant_on_fiber_direction_ratios_algebraic
    (p q : MvPolynomial (Fin 4) K) (hp : p ≠ 0) (hq : q ≠ 0) (hrel : IsRelPrime p q)
    {D : ℕ} (hD : 0 < D) (hpH : p.IsHomogeneous D) (hqH : q.IsHomogeneous D)
    (hpw : p.degreeOf (Fin.last 3) = 0) (hqw : q.degreeOf (Fin.last 3) = 0)
    (t : G) (ht : Transcendental E t) (z : Fin 4 → G) (x A : Fin 3 → E)
    (hx : ∀ i : Fin 3, z i.castSucc = algebraMap E G (x i) + algebraMap E G (A i) * t)
    (cp cq : E) (hcp : aeval z p = algebraMap E G cp) (hcq : aeval z q = algebraMap E G cq)
    (j : Fin 3) (hj : A j ≠ 0) : ∀ i : Fin 3, IsAlgebraic K (A i / A j) := by
  obtain ⟨p₀, q₀, hp₀, _hq₀, hrel₀, hp₀H, hq₀H, hpvalue, hqvalue⟩ :=
    vertex_independent_coprime_pencil_constructs_ternary_pair p q hp hq hrel hpH hqH hpw hqw
  have hcp₀ : aeval (fun i : Fin 3 => z i.castSucc) p₀ = algebraMap E G cp := by
    rw [← hpvalue, aeval_rename] at hcp
    exact hcp
  have hcq₀ : aeval (fun i : Fin 3 => z i.castSucc) q₀ = algebraMap E G cq := by
    rw [← hqvalue, aeval_rename] at hcq
    exact hcq
  have hpA := homogeneous_invariant_constant_on_actual_affine_line_direction_zero
    p₀ hD hp₀H t ht (fun i : Fin 3 => z i.castSucc) x A hx cp hcp₀
  have hqA := homogeneous_invariant_constant_on_actual_affine_line_direction_zero
    q₀ hD hq₀H t ht (fun i : Fin 3 => z i.castSucc) x A hx cq hcq₀
  exact coprime_ternary_homogeneous_common_zero_ratios_algebraic p₀ q₀ hp₀ hrel₀ hp₀H hq₀H A j hj hpA hqA

end DimensionFourDependence
