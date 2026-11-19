import DimensionFourDependence.ParametricDerivationMinor

/-! # Every independent constant covector pair detects the moving output plane -/

namespace DimensionFourDependence

set_option maxHeartbeats 2500000

variable {K F : Type*} [Field K] [CharZero K] [Field F] [Algebra K F] {n : ℕ}

/-- Independence of the original common-scalar values forces
independence of their original parameter polynomials. -/
theorem independent_scaled_parameter_values_parameter_family_independent
    (Y : Fin n → F) (hY : LinearIndependent K Y) (s t : F)
    (v : Fin n → Polynomial K) (hrep : ∀ i, Y i = s * Polynomial.aeval t (v i)) :
    LinearIndependent K v := by
  let L : Polynomial K →ₗ[K] F :=
    { toFun := fun P => s * Polynomial.aeval t P
      map_add' := by intro P Q; simp [mul_add]
      map_smul' := by intro c P; simp [Algebra.smul_def, mul_left_comm] }
  apply LinearIndependent.of_comp L
  convert hY using 1
  funext i
  exact (hrep i).symm

/-- Independent covectors give two independent combinations of any
independent original parameter-polynomial family. -/
theorem independent_covectors_parameter_combinations_independent
    (v : Fin n → Polynomial K) (hv : LinearIndependent K v)
    (μ ν : Fin n → K) (hμν : LinearIndependent K ![μ, ν]) :
    LinearIndependent K ![∑ i, μ i • v i, ∑ i, ν i • v i] := by
  rw [LinearIndependent.pair_iff]
  intro a b hab
  have hcoeff : ∀ i, a * μ i + b * ν i = 0 := by
    apply Fintype.linearIndependent_iff.mp hv
    convert hab using 1
    simp only [Finset.smul_sum, ← Finset.sum_add_distrib, add_smul, mul_smul]
  have hrel : a • μ + b • ν = 0 := by
    funext i
    exact hcoeff i
  exact (LinearIndependent.pair_iff.mp hμν) a b hrel

/-- The exact common-scalar parameter presentation implies that
every independent original covector pair has a nonzero minor on the
output and its derivative along the actual vector field. No orders,
leading coefficients or small-parameter inequalities are supplied. -/
theorem independent_covectors_scaled_parameter_orbit_minor_ne_zero
    (D : Derivation K F F) (Y : Fin n → F) (hY : LinearIndependent K Y)
    (s t : F) (hs : s ≠ 0) (ht : D t ≠ 0)
    (v : Fin n → Polynomial K) (hrep : ∀ i, Y i = s * Polynomial.aeval t (v i))
    (μ ν : Fin n → K) (hμν : LinearIndependent K ![μ, ν]) :
    (∑ i, μ i • Y i) * (∑ i, ν i • D (Y i)) -
      (∑ i, ν i • Y i) * (∑ i, μ i • D (Y i)) ≠ 0 := by
  have hv := independent_scaled_parameter_values_parameter_family_independent Y hY s t v hrep
  have hfg := independent_covectors_parameter_combinations_independent v hv μ ν hμν
  have hsum (c : Fin n → K) :
      (∑ i, c i • Y i) = s * Polynomial.aeval t (∑ i, c i • v i) := by
    simp only [hrep, map_sum, map_smul, Finset.mul_sum, Algebra.smul_def]
    apply Finset.sum_congr rfl
    intro i _
    rw [map_mul, (Polynomial.aeval t).commutes]
    ring
  have hder (c : Fin n → K) : (∑ i, c i • D (Y i)) = D (∑ i, c i • Y i) := by
    simp only [map_sum, D.map_smul]
  rw [hder, hder, hsum, hsum]
  exact independent_scaled_parameter_derivation_minor_ne_zero D s t hs ht _ _ hfg

end DimensionFourDependence
