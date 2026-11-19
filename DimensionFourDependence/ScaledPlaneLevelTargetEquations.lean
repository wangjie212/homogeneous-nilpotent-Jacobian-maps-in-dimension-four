import DimensionFourDependence.FixedVertexScaledDualOutputBasis
import DimensionFourDependence.NativePolynomialGermPointEquations

/-! # The scaled quotient levels have exactly the original output-target equations -/

namespace DimensionFourDependence

open MvPolynomial Matrix AlgebraicGeometry TopologicalSpace

attribute [local instance] MvPolynomial.gradedAlgebra

universe u

set_option quotPrecheck false
set_option maxHeartbeats 3000000
set_option synthInstance.maxHeartbeats 100000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- Combining the component target equations gives the corresponding
output-linear equation with its exact target value. -/
theorem output_linear_level_equation_eq_sum
    {E : Type*} [CommRing E] (P : Fin 4 → MvPolynomial (Fin 4) E)
    (ν Y : Fin 4 → E) (B : MvPolynomial (Fin 4) E) :
    (∑ i, C (ν i) * P i) - C (ν ⬝ᵥ Y) * B =
      ∑ i, C (ν i) * (P i - C (Y i) * B) := by
  simp only [mul_sub, Finset.sum_sub_distrib, ← mul_assoc, ← map_mul,
    ← Finset.sum_mul, ← map_sum, dotProduct]

variable {K : Type u} [Field K] [CharZero K]
    (H : Fin 4 → MvPolynomial (Fin 4) K) (I : ImageRelationWitness H)
    (E : Type u) [Field E] [Algebra (closedGaussParameterField H I) E]
    [Algebra.IsAlgebraic (closedGaussParameterField H I) E]
    {d : ℕ} (hH : IsHomogMap H d)
    (e : RatFunc K ≃ₐ[K] closedGaussParameterField H I)

local notation "N" => extendedClosedGaussNormalizationScheme H I E hH e
local notation "w" => extendedClosedGaussNormalizationHyperplaneWeight H I E hH e
local notation "V" a:max => extendedClosedGaussNormalizationChartOpen H I E hH e (finSuccEquiv' a)
local notation "f" => extendedClosedGaussNormalizationProjectiveMap H I E hH e
local notation "ι" => extendedClosedGaussSourceCoefficientHom H I E
local notation "O" => extendedClosedGaussOutputLinearPolynomial H I E

local instance scaledPlaneLevelTargetEquationsIntegral : IsIntegral N :=
  extendedClosedGaussNormalizationScheme_isIntegral H I E hH e
noncomputable local instance scaledPlaneLevelTargetEquationsAlgebra : Algebra E (N).functionField :=
  extendedClosedGaussOwnFunctionFieldAlgebra H I E hH e

/-- Every homogeneous identity in the native function field is an
equation of every actual projective source image point. -/
theorem native_homogeneous_zero_mem_every_projective_image
    (P : MvPolynomial (Fin 4) E) {D : ℕ} (hP : P.IsHomogeneous D)
    (hzero : aeval (w) P = 0) (y : N) : P ∈ ((f) y).asHomogeneousIdeal := by
  obtain ⟨a, ha⟩ := TopologicalSpace.Opens.mem_iSup.mp ((extendedClosedGaussNormalizationChartOpen_iSup H I E hH e).ge
    (show y ∈ ⊤ from trivial))
  apply (native_polynomial_germ_mem_maximal_iff_projective_equation H I E hH e P hP y a ha).mp
  rw [(extendedClosedGaussPolynomialCoefficientGerm_eq_zero_iff H I E hH e P hP y a ha).mpr hzero]
  exact Ideal.zero_mem _

variable (hd : 0 < d) (hind : ¬ComponentsDependent H) (hGauss : gaussImageDimension H I = 1)
    (hvertex : rationalImageNormal H I.equation (Fin.last 3) = 0)

local notation "A₀" => extendedClosedGaussChosenRulingMatrix H I E hH hd hind hGauss
local notation "W₀" => LinearMap.ker (A₀).toLin'
local notation "L₀" => linearFormPolynomial ((A₀) 0)

include hvertex

/-- The original scaled-plane data construct a dual target basis.
At every normalization point, its quotient level equation is equivalent
to all four original homogeneous component equations with target
c bS + λ bN. This establishes the target coordinate on the ruling. -/
theorem actual_scaled_plane_levels_iff_original_output_target_equations
    (s n : Fin 4 → E) (hs : s (Fin.last 3) ≠ 0) (hnlast : n (Fin.last 3) = 0)
    (hn : aeval (w) ((O) n) ≠ 0) (c : E)
    (hpower : aeval (w) ((O) s) = algebraMap E (N).functionField c * (aeval (w) (L₀)) ^ d) :
    ∃ bS bN : Fin 4 → E, LinearIndependent E ![bS, bN] ∧ bS ∈ W₀ ∧ bN ∈ W₀ ∧
      s ⬝ᵥ bS = 1 ∧ n ⬝ᵥ bS = 0 ∧ s ⬝ᵥ bN = 0 ∧ n ⬝ᵥ bN = 1 ∧
      ∀ (t : E) (y : N),
        ((O) n - C t * (L₀) ^ d ∈ ((f) y).asHomogeneousIdeal ↔
          ∀ i : Fin 4, MvPolynomial.map (ι) (H i) -
            C (c * bS i + t * bN i) * (L₀) ^ d ∈ ((f) y).asHomogeneousIdeal) := by
  obtain ⟨bS, bN, hLI, hbS, hbN, hsS, hnS, hsN, hnN, hspan⟩ :=
    fixed_vertex_scaled_covectors_construct_dual_output_basis
      H I E hH e hd hind hGauss hvertex s n hs hnlast hn
  refine ⟨bS, bN, hLI, hbS, hbN, hsS, hnS, hsN, hnN, ?_⟩
  intro t y
  let Y : Fin 4 → E := fun i => c * bS i + t * bN i
  have hY : n ⬝ᵥ Y = t := by
    change (∑ i, n i * (c * bS i + t * bN i)) = t
    simp_rw [mul_add, mul_left_comm (n _) c, mul_left_comm (n _) t]
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
    change c * (n ⬝ᵥ bS) + t * (n ⬝ᵥ bN) = t
    rw [hnS, hnN, mul_zero, mul_one, zero_add]
  constructor
  · intro hlevel i
    change MvPolynomial.map (ι) (H i) - C (c * bS i + t * bN i) * (L₀) ^ d ∈
      ((f) y).asHomogeneousIdeal.toIdeal
    let Q := MvPolynomial.map (ι) (H i) - C (Y i) * (L₀) ^ d -
      C (bN i) * ((O) n - C t * (L₀) ^ d)
    have hQ : Q.IsHomogeneous d :=
      (((hH i).map _).sub (by simpa only [one_mul] using
        ((linearFormPolynomial_homogeneous _).pow d).C_mul (Y i))).sub
          (((extendedClosedGaussOutputLinearPolynomial_homogeneous H I E hH n).sub
            (by simpa only [one_mul] using ((linearFormPolynomial_homogeneous _).pow d).C_mul t)).C_mul (bN i))
    have hzero : aeval (w) Q = 0 := by
      simp only [Q, Y, map_sub, map_mul, map_pow, aeval_C, map_add, hspan i, hpower]
      ring
    have heq := native_homogeneous_zero_mem_every_projective_image H I E hH e Q hQ hzero y
    have hmul := ((f) y).asHomogeneousIdeal.toIdeal.mul_mem_left (C (bN i)) hlevel
    have hsum := ((f) y).asHomogeneousIdeal.toIdeal.add_mem heq hmul
    simpa only [Q, Y, sub_add_cancel] using hsum
  · intro htarget
    change (O) n - C t * (L₀) ^ d ∈ ((f) y).asHomogeneousIdeal.toIdeal
    have hsum := ((f) y).asHomogeneousIdeal.toIdeal.sum_mem
      (fun (i : Fin 4) (_ : i ∈ Finset.univ) =>
        ((f) y).asHomogeneousIdeal.toIdeal.mul_mem_left (C (n i)) (htarget i))
    rw [← output_linear_level_equation_eq_sum, hY] at hsum
    simpa only [extendedClosedGaussOutputLinearPolynomial, MvPolynomial.smul_eq_C_mul] using hsum

end DimensionFourDependence
