import DimensionFourDependence.ProportionalConeKernelDirection
import DimensionFourDependence.ActualFiberSourceFrame

/-! # An actual nonlinear parabolic fiber cannot have the directrix's projected direction -/

namespace DimensionFourDependence

open MvPolynomial Matrix

set_option maxHeartbeats 6000000
set_option synthInstance.maxHeartbeats 100000
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

variable {K E F : Type*} [Field K] [CharZero K] [Field E] [Field F] [CharZero F]
    [Algebra K E] [Algebra K F] [Algebra E F] [IsScalarTower K E F]
    [Algebra (FractionRing (MvPolynomial (Fin 4) K)) F]
    [IsScalarTower K (FractionRing (MvPolynomial (Fin 4) K)) F]
    [Algebra.IsAlgebraic (FractionRing (MvPolynomial (Fin 4) K)) F]

local notation "S₀" => FractionRing (MvPolynomial (Fin 4) K)
local notation "x₀" => fun i : Fin 4 => algebraMap S₀ F (rationalCoordinate (K := K) i)
local notation "D₀" => algebraicPartial (K := K) F

/-- Original nilpotence and rank three exclude a projected actual
parabolic fiber direction proportional to the parameter-algebraic
directrix. Only the first three scalar cone formulas are used; neither
the last cone formula, normal jets nor a chosen kernel vector is supplied. -/
theorem actual_nonlinear_parabolic_cone_direction_not_proportional
    (H : Fin 4 → MvPolynomial (Fin 4) K) (hN : IsNilpotent (jac H))
    (hrank : polyRank (jac H) = 3) (p : RatFunc K →ₐ[K] F)
    (hp : ∃ τ : E, p RatFunc.X = algebraMap E F τ)
    (ht : (D₀) (Fin.last 3) (p RatFunc.X) ≠ 0)
    (t : F) (htrans : Transcendental E t) (x A V : Fin 3 → E) (w B C f y : E)
    (hC : C ≠ 0) (hV0 : V ≠ 0)
    (hline : ∀ i : Fin 3, (x₀) i.castSucc = algebraMap E F (x i) + algebraMap E F (A i) * t)
    (hparabola : (x₀) (Fin.last 3) = algebraMap E F w + algebraMap E F B * t + algebraMap E F C * t ^ 2)
    (hy : algebraMap S₀ F (algebraMap (MvPolynomial (Fin 4) K) S₀ (H (Fin.last 3))) = algebraMap E F y)
    (hfirst : ∀ i : Fin 3, algebraMap S₀ F (algebraMap (MvPolynomial (Fin 4) K) S₀ (H i.castSucc)) =
      algebraMap E F (V i) * algebraMap E F f)
    (hV : ∀ i, IsAlgebraic p.fieldRange (algebraMap E F (V i)))
    (s : E) (hA : ∀ i : Fin 3, A i = s * V i) : False := by
  letI : CharZero E := charZero_of_injective_algebraMap (algebraMap K E).injective
  obtain ⟨Δ, hΔt⟩ := exists_derivation_apply_eq_one_of_transcendental t htrans
  let D : Derivation K F F := Δ.restrictScalars K
  have hconst (c : E) : D (algebraMap E F c) = 0 := Δ.map_algebraMap c
  have hDp : D (p RatFunc.X) = 0 := by obtain ⟨τ, hτ⟩ := hp; rw [hτ, hconst]
  have hDx (i : Fin 3) : D ((x₀) i.castSucc) = algebraMap E F (A i) :=
    affine_fiber_coordinate_derivative Δ t hΔt (x i) (A i) _ (hline i)
  have hnonzero : ¬ ∀ i : Fin 3, D ((x₀) i.castSucc) = 0 := by
    intro hz
    have hD0 : D = 0 := by
      apply algebraic_source_parameter_transverse_derivation_ext (p RatFunc.X) ht
      · simpa only [Derivation.zero_apply] using hDp
      · intro i
        simpa only [Derivation.zero_apply] using hz i
    have he : D t = 1 := hΔt
    rw [hD0, Derivation.zero_apply] at he
    exact zero_ne_one he
  have hs : s ≠ 0 := by
    intro hs0
    apply hnonzero
    intro i
    rw [hDx, hA, hs0, zero_mul, map_zero]
  let sF := algebraMap E F s
  have hsF : sF ≠ 0 := by simpa only [map_zero] using (algebraMap E F).injective.ne hs
  let U' : Derivation K F F := sF⁻¹ • D
  let U := coordinateEuler (fun i => algebraMap E F (V i)) (transverseParameterPartial (D₀) (p RatFunc.X))
  have hU'p : U' (p RatFunc.X) = 0 := by
    change sF⁻¹ * D (p RatFunc.X) = 0
    rw [hDp, mul_zero]
  have hU'x (i : Fin 3) : U' ((x₀) i.castSucc) = algebraMap E F (V i) := by
    change sF⁻¹ * D ((x₀) i.castSucc) = _
    rw [hDx, hA, map_mul]
    change sF⁻¹ * (sF * algebraMap E F (V i)) = _
    rw [← mul_assoc, inv_mul_cancel₀ hsF, one_mul]
  have hframe : U' = U := algebraic_source_fixed_parameter_direction_eq_transverse_frame
    (p RatFunc.X) ht U' hU'p _ hU'x
  have hUf : U (algebraMap E F f) = 0 := by
    rw [← hframe]
    change sF⁻¹ * D (algebraMap E F f) = 0
    rw [hconst, mul_zero]
  have hUh : U (algebraMap S₀ F (algebraMap (MvPolynomial (Fin 4) K) S₀ (H (Fin.last 3)))) = 0 := by
    rw [hy, ← hframe]
    change sF⁻¹ * D (algebraMap E F y) = 0
    rw [hconst, mul_zero]
  have hVmap0 : (fun i => algebraMap E F (V i)) ≠ 0 := by
    intro hz
    apply hV0
    funext i
    apply (algebraMap E F).injective
    simpa only [map_zero, Pi.zero_apply] using congrFun hz i
  have hUacc := original_output_constant_directrix_direction_vertex_acceleration_zero p H hN hrank ht
    (fun i => algebraMap E F (V i)) hVmap0 (algebraMap E F f) hV hfirst hUf hUh
  have hD_eq (a : F) : D a = sF * U a := by
    rw [← hframe]
    change D a = sF * (sF⁻¹ * D a)
    rw [← mul_assoc, mul_inv_cancel₀ hsF, one_mul]
  have hDacc0 : D (D ((x₀) (Fin.last 3))) = 0 := by
    rw [hD_eq ((x₀) (Fin.last 3)), D.leibniz, hconst, hD_eq (U ((x₀) (Fin.last 3))), hUacc]
    simp
  have hDacc := (parabolic_fiber_vertex_derivatives Δ t hΔt w B C _ hparabola).2
  change D (D ((x₀) (Fin.last 3))) = 2 * algebraMap E F C at hDacc
  apply mul_ne_zero (by norm_num : (2 : F) ≠ 0)
    (by simpa only [map_zero] using (algebraMap E F).injective.ne hC)
  exact hDacc.symm.trans hDacc0

/-- The actual nonlinear parabola and original nilpotent rank-three
map construct independence of the projected fiber and directrix
directions, without assuming parameter algebraicity of the fiber direction. -/
theorem actual_nonlinear_parabolic_cone_constructs_independent_projected_directions
    (H : Fin 4 → MvPolynomial (Fin 4) K) (hN : IsNilpotent (jac H))
    (hrank : polyRank (jac H) = 3) (p : RatFunc K →ₐ[K] F)
    (hp : ∃ τ : E, p RatFunc.X = algebraMap E F τ)
    (ht : (D₀) (Fin.last 3) (p RatFunc.X) ≠ 0)
    (t : F) (htrans : Transcendental E t) (x A V : Fin 3 → E) (w B C f y : E)
    (hC : C ≠ 0) (hV0 : V ≠ 0)
    (hline : ∀ i : Fin 3, (x₀) i.castSucc = algebraMap E F (x i) + algebraMap E F (A i) * t)
    (hparabola : (x₀) (Fin.last 3) = algebraMap E F w + algebraMap E F B * t + algebraMap E F C * t ^ 2)
    (hy : algebraMap S₀ F (algebraMap (MvPolynomial (Fin 4) K) S₀ (H (Fin.last 3))) = algebraMap E F y)
    (hfirst : ∀ i : Fin 3, algebraMap S₀ F (algebraMap (MvPolynomial (Fin 4) K) S₀ (H i.castSucc)) =
      algebraMap E F (V i) * algebraMap E F f)
    (hV : ∀ i, IsAlgebraic p.fieldRange (algebraMap E F (V i))) :
    LinearIndependent E ![V, A] := by
  apply (LinearIndependent.pair_iff' hV0).mpr
  intro s hs
  exact actual_nonlinear_parabolic_cone_direction_not_proportional H hN hrank p hp ht t htrans
    x A V w B C f y hC hV0 hline hparabola hy hfirst hV s
    (fun i => by simpa only [Pi.smul_apply, smul_eq_mul] using (congrFun hs i).symm)

end DimensionFourDependence
