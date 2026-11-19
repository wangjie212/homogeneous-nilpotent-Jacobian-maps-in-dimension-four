import DimensionFourDependence.FullDimensionAffineLineParameter
import DimensionFourDependence.AffineLinePolynomialRestriction
import DimensionFourDependence.AffineLineKernelConstancy
import DimensionFourDependence.OriginalPrimitiveKernelNonvanishing

/-! # Actual affine-line fibers give zero acceleration of the original primitive kernel -/

namespace DimensionFourDependence

open MvPolynomial Matrix

universe u
set_option maxHeartbeats 3000000
set_option synthInstance.maxHeartbeats 100000

variable {K : Type u} [Field K] [CharZero K]
local notation "R₀" => MvPolynomial (Fin 4) K

/-- One actual geometric generic component on an affine line forces
zero acceleration of the original primitive polynomial kernel.
The parameter's transcendence, original Jacobian rank, and absence of
zeros of the kernel are all constructed from the original source. -/
theorem original_geometric_affine_line_primitive_kernel_zero_acceleration
    (H : Fin 4 → R₀) (hrank : polyRank (jac H) = 3)
    (u : Fin 4 → R₀) {e : ℕ} (hu : IsPrimRightKernel (jac H) u e)
    (E : Type u) [Field E] [IsAlgClosed E]
    [Algebra (polynomialOutputField H) E] [Algebra K E]
    [IsScalarTower K (polynomialOutputField H) E]
    [Algebra.IsAlgebraic (polynomialOutputField H) E]
    (P : Ideal (MvPolynomial (Fin 4) E)) [P.IsPrime]
    (hP : P ∈ (extendCoefficientIdeal E (fiberVanishingIdeal
      (L := polynomialOutputField H) (rationalCoordinate (K := K) (n := 4)))).minimalPrimes)
    (hline : LiesInAffineLine (E := E) (primeQuotientCoordinate P)) :
    jac u *ᵥ u = 0 := by
  classical
  let G := FractionRing (MvPolynomial (Fin 4) E ⧸ P)
  let x := primeQuotientCoordinate P
  let ev : R₀ →ₐ[K] G := aeval x
  obtain ⟨a, v, hv, t, hpos⟩ := hline
  have ht : Transcendental E t :=
    original_geometric_generic_component_affine_line_parameter_transcendental H hrank P hP a v t hpos
  let R : R₀ → Polynomial E := affineLinePolynomialRestriction a v
  have hposfun : (fun i => algebraMap E G (a i) + algebraMap E G (v i) * t) = x :=
    (funext hpos).symm
  have hrest (p : R₀) : Polynomial.aeval t (R p) = ev p := by
    exact (affineLinePolynomialRestriction_aeval a v t p).trans
      (congrArg (fun z => aeval z p) hposfun)
  have hy (i : Fin 4) : ev (H i) = algebraMap E G (genericOutputValue H E i) := by
    simpa only [aeval_map_coefficients] using geometric_component_generic_output_evaluation H E P hP i
  have hHline (i : Fin 4) : R (H i) = Polynomial.C (genericOutputValue H E i) := by
    apply (transcendental_iff_injective.mp ht)
    rw [hrest, Polynomial.aeval_C, hy]
  have hder (p : R₀) : (∑ j, ev (pderiv j p) * algebraMap E G (v j)) =
      Polynomial.aeval t ((R p).derivative) := by
    rw [affineLinePolynomialRestriction_derivative]
    simp only [map_sum, map_mul, Polynomial.aeval_C]
    change (∑ j, ev (pderiv j p) * algebraMap E G (v j)) =
      ∑ j, Polynomial.aeval t (R (pderiv j p)) * algebraMap E G (v j)
    simp only [hrest]
  let A : Matrix (Fin 4) (Fin 4) (Polynomial E) := Matrix.of fun i j => R (pderiv j (H i))
  have hA : A.map (Polynomial.aeval t : Polynomial E →ₐ[E] G) = (jac H).map ev := by
    ext i j
    exact hrest (pderiv j (H i))
  have hArank : (A.map (Polynomial.aeval t : Polynomial E →ₐ[E] G)).rank = 3 := by
    rw [hA, geometric_component_original_evaluated_jacobian_rank H E P hP, hrank]
  have hAv : A.map (Polynomial.aeval t : Polynomial E →ₐ[E] G) *ᵥ
      (fun i => algebraMap E G (v i)) = 0 := by
    funext i
    change (∑ j, Polynomial.aeval t (R (pderiv j (H i))) * algebraMap E G (v j)) = 0
    simp only [hrest]
    rw [hder, hHline, Polynomial.derivative_C, map_zero]
  have hAU : A.map (Polynomial.aeval t : Polynomial E →ₐ[E] G) *ᵥ
      (fun i => Polynomial.aeval t (R (u i))) = 0 := by
    funext i
    change (∑ j, Polynomial.aeval t (R (pderiv j (H i))) * Polynomial.aeval t (R (u j))) = 0
    simp only [hrest]
    have he := congrArg ev (congrFun hu.ker i)
    simpa only [Matrix.mulVec, dotProduct, jac, Matrix.of_apply, map_sum, map_mul,
      Pi.zero_apply, map_zero] using he
  have hnozero (s : E) : (fun i => (R (u i)).eval s) ≠ 0 := by
    have hpoint (i : Fin 4) : aeval (fun j => a j + v j * s) (H i) = genericOutputValue H E i := by
      rw [← affineLinePolynomialRestriction_eval a v s]
      change (R (H i)).eval s = _
      rw [hHline, Polynomial.eval_C]
    have hn := original_rank_three_generic_output_point_primitive_vector_nonzero
      H hrank u hu.ne_zero hu.prim E (fun j => a j + v j * s) hpoint
    simpa only [R, affineLinePolynomialRestriction_eval] using hn
  obtain ⟨c, _hc, hconst⟩ := polynomial_line_rank_three_kernel_nowhere_zero_constant
    A (fun i => R (u i)) v hv t ht hArank hAv hAU hnozero
  have hzero (i : Fin 4) : ∑ j, ev (pderiv j (u i)) * algebraMap E G (v j) = 0 := by
    rw [hder, hconst, Polynomial.derivative_C, map_zero]
  have hvalue (j : Fin 4) : ev (u j) = algebraMap E G c * algebraMap E G (v j) := by
    rw [← hrest, hconst, Polynomial.aeval_C, map_mul]
  have hinj : Function.Injective ev := algebraicIndependent_iff_injective_aeval.mp
    (geometric_component_original_source_coordinates_algebraicIndependent H E P hP)
  funext i
  apply hinj
  change ev ((jac u *ᵥ u) i) = ev 0
  simp only [Matrix.mulVec, dotProduct, jac, Matrix.of_apply, map_sum, map_mul, map_zero]
  simp_rw [hvalue]
  calc
    (∑ j, ev (pderiv j (u i)) * (algebraMap E G c * algebraMap E G (v j))) =
        algebraMap E G c * ∑ j, ev (pderiv j (u i)) * algebraMap E G (v j) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      ring
    _ = 0 := by rw [hzero, mul_zero]

/-- The original homogeneous rank-three map constructs a primitive
homogeneous kernel with zero acceleration from an actual line component. -/
theorem original_homogeneous_affine_line_component_constructs_zero_acceleration_kernel
    (H : Fin 4 → R₀) {d : ℕ} (hH : IsHomogMap H d) (hrank : polyRank (jac H) = 3)
    (E : Type u) [Field E] [IsAlgClosed E]
    [Algebra (polynomialOutputField H) E] [Algebra K E]
    [IsScalarTower K (polynomialOutputField H) E]
    [Algebra.IsAlgebraic (polynomialOutputField H) E]
    (P : Ideal (MvPolynomial (Fin 4) E)) [P.IsPrime]
    (hP : P ∈ (extendCoefficientIdeal E (fiberVanishingIdeal
      (L := polynomialOutputField H) (rationalCoordinate (K := K) (n := 4)))).minimalPrimes)
    (hline : LiesInAffineLine (E := E) (primeQuotientCoordinate P)) :
    ∃ (u : Fin 4 → R₀) (e : ℕ), IsPrimRightKernel (jac H) u e ∧ jac u *ᵥ u = 0 := by
  obtain ⟨u, e, hu⟩ := exists_primRightKernel (jac H) (fun i j => (hH i).pderiv (i := j))
    (by rw [hrank]; norm_num)
  exact ⟨u, e, hu,
    original_geometric_affine_line_primitive_kernel_zero_acceleration H hrank u hu E P hP hline⟩

end DimensionFourDependence
