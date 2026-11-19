import DimensionFourDependence.GenericParameterPole

/-! # Polynomial vertex parameters force polynomial ternary coefficients

A reduced common coefficient denominator is constructed for each form.
At a constant root it would produce a polynomial reciprocal of the
already polynomial parameter. That would make the parameter scalar,
a contradiction. Over algebraically closed original constants the
common denominator is therefore constant, and scaling its numerator
constructs the full form over K[t].
-/

namespace DimensionFourDependence

variable {K L F σ : Type*} [Field K] [IsAlgClosed K] [Field L] [Field F]
    [Algebra K L] [Algebra K F] [Algebra L F] [IsScalarTower K L F]
    [Algebra (Polynomial L) F] [IsScalarTower L (Polynomial L) F]
    [IsFractionRing (Polynomial L) F]

/-- A generic ternary form with polynomial source value, evaluated at
a nonconstant polynomial vertex parameter, has all its coefficients in
K[t]. The entire coefficient polynomial is recovered under inclusion. -/
theorem polynomial_vertex_parameter_form_coefficients_are_polynomial
    (x : σ → L) (hx : AlgebraicIndependent K x) (f : RatFunc K →ₐ[K] F)
    (U : Polynomial L) (hUdegree : 0 < U.natDegree)
    (hU : algebraMap (Polynomial L) F U = f RatFunc.X)
    (P : MvPolynomial σ (RatFunc K)) (H : Polynomial L)
    (hvalue : MvPolynomial.eval₂ f.toRingHom (fun i => algebraMap L F (x i)) P =
      algebraMap (Polynomial L) F H) :
    ∃ Q : MvPolynomial σ (Polynomial K),
      MvPolynomial.map (algebraMap (Polynomial K) (RatFunc K)) Q = P := by
  classical
  have ht : ¬ ∃ c : L, algebraMap L F c = f RatFunc.X := by
    rintro ⟨c, hc⟩
    have hC : U = Polynomial.C c := by
      apply IsFractionRing.injective (Polynomial L) F
      rw [hU]
      change f RatFunc.X = algebraMap (Polynomial L) F (algebraMap L (Polynomial L) c)
      rw [← IsScalarTower.algebraMap_apply L (Polynomial L) F, hc]
    have hd := congrArg Polynomial.natDegree hC
    rw [Polynomial.natDegree_C] at hd
    omega
  obtain ⟨D, hD, N, hN, hpole⟩ := generic_parameter_form_constructs_reduced_pole_pullback
    x hx f ht P H hvalue
  have hDdegree : D.natDegree = 0 := by
    by_contra hdeg
    have hpos : 0 < D.degree := Polynomial.natDegree_pos_iff_degree_pos.mp (Nat.pos_of_ne_zero hdeg)
    obtain ⟨a, ha⟩ := IsAlgClosed.exists_root D hpos.ne'
    obtain ⟨V, _hVdegree, hV⟩ := hpole a ha
    have hta : f RatFunc.X ≠ algebraMap L F (algebraMap K L a) := fun hz => ht ⟨_, hz.symm⟩
    have hV' : algebraMap (Polynomial L) F V =
        (f RatFunc.X - algebraMap L F (algebraMap K L a))⁻¹ := by
      simpa only [← IsScalarTower.algebraMap_apply K L F] using hV
    exact ht (polynomial_parameter_and_reciprocal_force_scalar
      (f RatFunc.X) (algebraMap K L a) hta U V hU hV')
  have hDc : D = Polynomial.C (D.coeff 0) := Polynomial.eq_C_of_natDegree_eq_zero hDdegree
  have hDc0 : D.coeff 0 ≠ 0 := by intro hz; apply hD; rw [hDc, hz, map_zero]
  have hDmap : algebraMap (Polynomial K) (RatFunc K) D =
      algebraMap K (RatFunc K) (D.coeff 0) := by
    simpa [RatFunc.algebraMap_C] using congrArg (algebraMap (Polynomial K) (RatFunc K)) hDc
  have hcancel : algebraMap (Polynomial K) (RatFunc K) (Polynomial.C ((D.coeff 0)⁻¹)) *
      algebraMap (Polynomial K) (RatFunc K) D = 1 := by
    rw [hDmap]
    change algebraMap K (RatFunc K) ((D.coeff 0)⁻¹) * algebraMap K (RatFunc K) (D.coeff 0) = 1
    rw [← map_mul, inv_mul_cancel₀ hDc0, map_one]
  refine ⟨MvPolynomial.C (Polynomial.C ((D.coeff 0)⁻¹)) * N, ?_⟩
  rw [map_mul, MvPolynomial.map_C, hN, ← mul_assoc, ← map_mul, hcancel, map_one, one_mul]

/-- The lift retains the original homogeneous source degree, since
coefficient inclusion is injective. -/
theorem polynomial_vertex_parameter_homogeneous_form_coefficients_are_polynomial
    (x : σ → L) (hx : AlgebraicIndependent K x) (f : RatFunc K →ₐ[K] F)
    (U : Polynomial L) (hUdegree : 0 < U.natDegree)
    (hU : algebraMap (Polynomial L) F U = f RatFunc.X)
    (P : MvPolynomial σ (RatFunc K)) {d : ℕ} (hP : P.IsHomogeneous d)
    (H : Polynomial L)
    (hvalue : MvPolynomial.eval₂ f.toRingHom (fun i => algebraMap L F (x i)) P =
      algebraMap (Polynomial L) F H) :
    ∃ Q : MvPolynomial σ (Polynomial K), Q.IsHomogeneous d ∧
      MvPolynomial.map (algebraMap (Polynomial K) (RatFunc K)) Q = P := by
  obtain ⟨Q, hQ⟩ := polynomial_vertex_parameter_form_coefficients_are_polynomial
    x hx f U hUdegree hU P H hvalue
  exact ⟨Q, MvPolynomial.IsHomogeneous.of_map (RatFunc.algebraMap_injective K)
    (by rw [hQ]; exact hP), hQ⟩

end DimensionFourDependence
