import DimensionFourDependence.RankThreeDerivationKernel

/-! # The original rank-three map constructs nonzero differentiation along the directrix -/

namespace DimensionFourDependence

open MvPolynomial Matrix

set_option maxHeartbeats 5000000
set_option synthInstance.maxHeartbeats 100000
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

variable {K F : Type*} [Field K] [CharZero K] [Field F] [CharZero F] [Algebra K F]
    [Algebra (FractionRing (MvPolynomial (Fin 4) K)) F]
    [IsScalarTower K (FractionRing (MvPolynomial (Fin 4) K)) F]
    [Algebra.IsAlgebraic (FractionRing (MvPolynomial (Fin 4) K)) F]

local notation "S₀" => FractionRing (MvPolynomial (Fin 4) K)
local notation "x₀" => fun i : Fin 4 => algebraMap S₀ F (rationalCoordinate (K := K) i)
local notation "D₀" => algebraicPartial (K := K) F

/-- If the projected fiber direction is independent of the actual
directrix, rank three forces f_V != 0. Otherwise the directrix direction
would give a second independent output-constant kernel derivation.
No independence of output functions or their gradients is supplied. -/
theorem original_rank_three_cone_constructs_nonzero_directrix_derivative
    (H : Fin 4 → MvPolynomial (Fin 4) K) (hrank : polyRank (jac H) = 3)
    (p : RatFunc K →ₐ[K] F) (ht : (D₀) (Fin.last 3) (p RatFunc.X) ≠ 0)
    (D : Derivation K F F) (A V ν : Fin 3 → F)
    (hDx : ∀ i : Fin 3, D ((x₀) i.castSucc) = A i)
    (hDQ : ∀ i : Fin 4, D (algebraMap S₀ F (algebraMap (MvPolynomial (Fin 4) K) S₀ (H i))) = 0)
    (hVA : LinearIndependent F ![V, A])
    {d : ℕ} (hd : 0 < d) (r f a b L : F) (hr : r ≠ 0) (hf : f = r ^ d)
    (hfirst : ∀ i : Fin 3, algebraMap S₀ F (algebraMap (MvPolynomial (Fin 4) K) S₀ (H i.castSucc)) = V i * f)
    (hlast : algebraMap S₀ F (algebraMap (MvPolynomial (Fin 4) K) S₀ (H (Fin.last 3))) =
      a * f + b * r ^ (d - 1) * L)
    (hV : ∀ i, IsAlgebraic p.fieldRange (V i)) (hν : ∀ i, IsAlgebraic p.fieldRange (ν i))
    (ha : IsAlgebraic p.fieldRange a) (hb : IsAlgebraic p.fieldRange b)
    (hL : L = ν ⬝ᵥ (fun i : Fin 3 => (x₀) i.castSucc)) (hνV : ν ⬝ᵥ V = 0) :
    (fun i => transverseParameterPartial (D₀) (p RatFunc.X) i f) ⬝ᵥ V ≠ 0 := by
  let δ := transverseParameterPartial (D₀) (p RatFunc.X)
  let U := coordinateEuler V δ
  have hfixed (c : F) (hc : IsAlgebraic p.fieldRange c) : U c = 0 := by
    simp only [U, δ, coordinateEuler_apply,
      transverse_parameter_partial_kills_algebraic_coefficient (D₀) p ht c hc,
      mul_zero, Finset.sum_const_zero]
  have hUx (i : Fin 3) : U ((x₀) i.castSucc) = V i :=
    coordinate_direction_coordinate δ (fun i : Fin 3 => (x₀) i.castSucc) V
      (vertex_parameter_derivation_frame_coordinate_values (D₀) (x₀)
        (algebraicPartial_coordinate F) (p RatFunc.X)).2.1 i
  have hUL : U L = 0 := by
    rw [hL, derivation_dotProduct]
    simp only [hfixed _ (hν _), hUx, dotProduct, zero_mul, Finset.sum_const_zero, zero_add]
    exact hνV
  intro hz
  have hUf : U f = 0 := (coordinate_direction_apply_eq_gradient_pairing δ V f).trans hz
  have hUQ : ∀ i : Fin 4, U (algebraMap S₀ F
      (algebraMap (MvPolynomial (Fin 4) K) S₀ (H i))) = 0 := by
    intro i
    refine Fin.lastCases ?_ (fun i => ?_) i
    · rw [cone_root_fixed_direction_derivative_identity U hd r f _ a b L hr hf hlast
        (hfixed a ha) (hfixed b hb) hUL, hUf, mul_zero]
    · rw [hfirst, U.leibniz, hfixed _ (hV i), hUf]
      simp only [smul_eq_mul, zero_mul, mul_zero, add_zero]
  have hdep := algebraic_source_output_constant_derivations_projected_pair_not_independent
    H hrank U D hUQ hDQ
  apply hdep
  simpa only [hUx, hDx] using hVA

end DimensionFourDependence
