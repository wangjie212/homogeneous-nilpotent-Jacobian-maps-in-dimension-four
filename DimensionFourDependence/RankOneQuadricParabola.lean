import DimensionFourDependence.ParabolaFromAffineSquare
import DimensionFourDependence.TwoConstantCovectorsLine
import DimensionFourDependence.RankOneBoundaryChart

/-! # An actual rank-one quadratic fiber equation constructs a parabola

The original rank-one equation makes the square of its normal coordinate
an actual affine-linear coordinate. Independent normal and linear parts
make that coordinate transcendental on a nonlinear curve when the
coefficient field is relatively algebraically closed. The actual degree
bound then constructs the nondegenerate quadratic parametrization.
-/

namespace DimensionFourDependence

open MvPolynomial Matrix

variable {L F : Type*} [Field L] [CharZero L] [Field F] [Algebra L F]

/-- The original rank-one quadratic fiber equation identifies an
actual affine-linear polynomial with the square of its normal coordinate. -/
theorem rank_one_quadric_constructs_affine_square
    (a g : Fin 3 → L) (N q : L) (hN : N ≠ 0) (x : Fin 3 → F)
    (hQ : aeval x (quadraticFiberPolynomial g (fun i j => -(a i * a j) / N) q) = 0) :
    aeval x (C (2 * N) * (linearFormPolynomial g - C q)) =
      (aeval x (linearFormPolynomial a)) ^ 2 := by
  let : CharZero F := charZero_of_injective_algebraMap (algebraMap L F).injective
  have hNF : algebraMap L F N ≠ 0 := (map_ne_zero (algebraMap L F)).mpr hN
  change aeval x (linearFormPolynomial g + C ((2 : L)⁻¹) *
    quadraticFormPolynomial (fun i j => -(a i * a j) / N) - C q) = 0 at hQ
  rw [quadraticFormPolynomial_rank_one_square,
    map_sub, map_add, map_mul, map_mul, map_pow, aeval_C, aeval_C, aeval_C] at hQ
  simp only [map_inv₀, map_neg, map_ofNat] at hQ
  simp only [map_mul, map_sub, aeval_C, map_ofNat]
  field_simp at hQ
  linear_combination hQ

/-- A nonlinear point of the actual rank-one quadric has a
transcendental normal coordinate when every algebraic source value
already belongs to the specified original coefficient field. -/
theorem rank_one_quadric_normal_coordinate_transcendental
    (hclosed : ∀ z : F, IsAlgebraic L z → ∃ r : L, algebraMap L F r = z)
    (a g : Fin 3 → L) (hag : LinearIndependent L ![a, g])
    (N q : L) (hN : N ≠ 0) (x : Fin 3 → F)
    (hQ : aeval x (quadraticFiberPolynomial g (fun i j => -(a i * a j) / N) q) = 0)
    (hline : ¬ LiesInAffineLine (E := L) x) :
    Transcendental L (aeval x (linearFormPolynomial a)) := by
  intro halg
  obtain ⟨r, hr⟩ := hclosed _ halg
  have he := rank_one_quadric_constructs_affine_square a g N q hN x hQ
  rw [← hr] at he
  have he' : algebraMap L F (2 * N) *
      ((fun i => algebraMap L F (g i)) ⬝ᵥ x - algebraMap L F q) = (algebraMap L F r) ^ 2 := by
    simpa only [map_mul, map_sub, aeval_C, linearFormPolynomial, map_sum, aeval_X,
      dotProduct] using he
  have hden : algebraMap L F (2 * N) ≠ 0 :=
    (map_ne_zero (algebraMap L F)).mpr (mul_ne_zero (by norm_num) hN)
  have hg : (fun i => algebraMap L F (g i)) ⬝ᵥ x = algebraMap L F (r ^ 2 / (2 * N) + q) := by
    rw [map_add, map_div₀, map_pow]
    have hd : (fun i => algebraMap L F (g i)) ⬝ᵥ x - algebraMap L F q =
        (algebraMap L F r) ^ 2 / algebraMap L F (2 * N) := by
      apply (eq_div_iff hden).mpr
      simpa only [mul_comm] using he'
    linear_combination hd
  apply hline
  apply two_constant_covectors_liesInAffineLine a g hag x r (r ^ 2 / (2 * N) + q) _ hg
  simpa only [linearFormPolynomial, map_sum, map_mul, aeval_C, aeval_X, dotProduct] using hr.symm

/-- The actual rank-one quadratic equation, coefficient closedness,
nonlinearity and degree bound construct an original-coordinate parabola. -/
theorem rank_one_quadric_degree_bound_constructs_parabola
    (hclosed : ∀ z : F, IsAlgebraic L z → ∃ r : L, algebraMap L F r = z)
    (a g : Fin 3 → L) (hag : LinearIndependent L ![a, g])
    (N q : L) (hN : N ≠ 0) (x : Fin 3 → F)
    (hQ : aeval x (quadraticFiberPolynomial g (fun i j => -(a i * a j) / N) q) = 0)
    {e : ℕ} (he : HasCurveHilbertDegree (projectiveConeIdeal (L := L) x) e) (hupper : e ≤ 2)
    (hline : ¬ LiesInAffineLine (E := L) x) : LiesInAffineParabola (L := L) x := by
  let T := linearFormPolynomial a
  let U : MvPolynomial (Fin 3) L := C (2 * N) * (linearFormPolynomial g - C q)
  have hU : U.totalDegree ≤ 1 := by
    apply (totalDegree_mul _ _).trans
    simpa only [totalDegree_C, zero_add] using
      (totalDegree_sub_C_le (linearFormPolynomial g) q).trans (linearFormPolynomial_totalDegree g)
  exact affine_square_coordinate_constructs_parabola x T U
    (linearFormPolynomial_totalDegree a) hU
    (rank_one_quadric_normal_coordinate_transcendental hclosed a g hag N q hN x hQ hline)
    (rank_one_quadric_constructs_affine_square a g N q hN x hQ) he hupper hline

end DimensionFourDependence
