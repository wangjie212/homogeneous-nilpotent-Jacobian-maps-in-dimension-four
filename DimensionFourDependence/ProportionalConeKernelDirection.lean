import DimensionFourDependence.TransverseFrameCommutation
import DimensionFourDependence.SquareZeroRankOneKernel
import DimensionFourDependence.ConstantKernelAcceleration
import DimensionFourDependence.ConeSquareZeroBlock
import DimensionFourDependence.RankThreeDerivationKernel
import DimensionFourDependence.RationalParameterAlgebraicDerivative

/-! # The directrix fiber direction constructs a constant nonzero Jacobian kernel vector -/

namespace DimensionFourDependence

open MvPolynomial Matrix

set_option quotPrecheck false
set_option maxHeartbeats 6000000
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

variable (p : RatFunc K →ₐ[K] F)

local notation "T" => vertexParameterPartial (D₀) (p RatFunc.X)
local notation "δ" => transverseParameterPartial (D₀) (p RatFunc.X)
local notation "Q₀" H:max => fun i : Fin 4 => algebraMap S₀ F (algebraMap (MvPolynomial (Fin 4) K) S₀ (H i))
local notation "N₀" H:max => Matrix.of (fun i j : Fin 4 => (D₀) j ((Q₀ H) i))

/-- If the directrix direction fixes both scalar outputs, original
nilpotence and rank three construct a nonzero Jacobian kernel vector
constant along that entire direction. The parameter derivative f_t
cancels from the vector; no constant-kernel hypothesis is supplied. -/
theorem original_directrix_output_constant_direction_constructs_constant_kernel
    (H : Fin 4 → MvPolynomial (Fin 4) K) (hN : IsNilpotent (jac H))
    (hrank : polyRank (jac H) = 3) (ht : (D₀) (Fin.last 3) (p RatFunc.X) ≠ 0)
    (V : Fin 3 → F) (f : F) (hV : ∀ i, IsAlgebraic p.fieldRange (V i))
    (hfirst : ∀ i : Fin 3, (Q₀ H) i.castSucc = V i * f)
    (hf : coordinateEuler V δ f = 0) (hh : coordinateEuler V δ ((Q₀ H) (Fin.last 3)) = 0) :
    ∃ u : Fin 4 → F, u ≠ 0 ∧ (N₀ H) *ᵥ u = 0 ∧ ∀ i, coordinateEuler V δ (u i) = 0 := by
  let U := coordinateEuler V δ
  let W : Fin 3 → F := fun i => T (V i)
  let fx : Fin 3 → F := fun i => δ i f
  let hx : Fin 3 → F := fun i => δ i ((Q₀ H) (Fin.last 3))
  let K₀ := coneFixedParameterJacobian V fx hx
  let c : Fin 4 → F := Fin.snoc (fun i => T f * V i + f * W i) (T ((Q₀ H) (Fin.last 3)))
  let l : Fin 4 → F := fun i => (D₀) i (p RatFunc.X)
  have hT := (vertex_parameter_derivation_frame_parameter_values (D₀) (p RatFunc.X) ht).1
  have hUt : U (p RatFunc.X) = 0 := by
    simp only [U, coordinateEuler_apply,
      (vertex_parameter_derivation_frame_parameter_values (D₀) (p RatFunc.X) ht).2,
      mul_zero, Finset.sum_const_zero]
  have hUcoeff (a : F) (ha : IsAlgebraic p.fieldRange a) : U a = 0 :=
    parameter_algebraic_coefficient_direction_constant p U hUt a ha
  have hVW (i : Fin 3) : U (V i) = 0 ∧ U (W i) = 0 :=
    ⟨hUcoeff _ (hV i), hUcoeff _
      (rational_parameter_derivative_preserves_algebraic_coefficients p T hT _ (hV i))⟩
  have hfxV : fx ⬝ᵥ V = 0 := (coordinate_direction_apply_eq_gradient_pairing δ V f).symm.trans hf
  have hhxV : hx ⬝ᵥ V = 0 :=
    (coordinate_direction_apply_eq_gradient_pairing δ V ((Q₀ H) (Fin.last 3))).symm.trans hh
  have hVfixed (i j : Fin 3) : δ j (V i) = 0 :=
    transverse_parameter_partial_kills_algebraic_coefficient (D₀) p ht _ (hV i) j
  have hJ : (N₀ H) = K₀ + Matrix.vecMulVec c l := by
    have he := vertex_parameter_frame_constructs_cone_jacobian_update (D₀) (p RatFunc.X) ht
      (Q₀ H) V W f 0 1 hfirst hVfixed (fun i => by simp only [zero_mul, one_mul, zero_add]; rfl)
    simpa only [coneParameterUpdateColumn, zero_mul, add_zero, one_mul] using he
  have hnil : IsNilpotent (K₀ + Matrix.vecMulVec c l) := by
    rw [← hJ]
    exact algebraic_original_source_partials_jacobian_nilpotent H hN
  have hr : (K₀ + Matrix.vecMulVec c l).rank = 3 := by
    rw [← hJ]
    exact algebraic_original_source_partials_jacobian_rank H hrank
  obtain ⟨hu0, hker⟩ := nilpotent_rank_three_square_zero_update_constructs_kernel_direction K₀ c l
    (cone_fixed_parameter_jacobian_square_zero V fx hx hfxV hhxV)
    ((cone_fixed_parameter_jacobian_trace V fx hx).trans hfxV) hnil hr
  have hUfx (i : Fin 3) : U (fx i) = 0 := parameter_algebraic_direction_fixes_transverse_gradient p ht V hV f hf i
  have hUhx (i : Fin 3) : U (hx i) = 0 :=
    parameter_algebraic_direction_fixes_transverse_gradient p ht V hV ((Q₀ H) (Fin.last 3)) hh i
  have hpair (a : Fin 3 → F) (ha : ∀ i, U (a i) = 0) : U (a ⬝ᵥ W) = 0 := by
    rw [derivation_dotProduct]
    simp only [ha, (hVW _).2, dotProduct, zero_mul, mul_zero, Finset.sum_const_zero, add_zero]
  have hcalc : K₀ *ᵥ c = Fin.snoc (fun i => f * (fx ⬝ᵥ W) * V i) (f * (hx ⬝ᵥ W)) :=
    square_zero_cone_block_mul_parameter_column V W fx hx (T f) f (T ((Q₀ H) (Fin.last 3))) hfxV hhxV
  refine ⟨K₀ *ᵥ c, hu0, ?_, ?_⟩
  · rw [hJ]; exact hker
  · intro i
    rw [hcalc]
    refine Fin.lastCases ?_ (fun i => ?_) i
    · rw [Fin.snoc_last, U.leibniz, hf, hpair hx hUhx]
      simp
    · rw [Fin.snoc_castSucc, U.leibniz, U.leibniz, hf, hpair fx hUfx, (hVW i).1]
      simp

/-- A directrix direction fixing the actual outputs has zero vertex
acceleration. Original nilpotence and rank construct its own nonzero
constant kernel direction; no affine-line or kernel-vector assumption is supplied. -/
theorem original_output_constant_directrix_direction_vertex_acceleration_zero
    (H : Fin 4 → MvPolynomial (Fin 4) K) (hN : IsNilpotent (jac H))
    (hrank : polyRank (jac H) = 3) (ht : (D₀) (Fin.last 3) (p RatFunc.X) ≠ 0)
    (V : Fin 3 → F) (hV0 : V ≠ 0) (f : F) (hV : ∀ i, IsAlgebraic p.fieldRange (V i))
    (hfirst : ∀ i : Fin 3, (Q₀ H) i.castSucc = V i * f)
    (hf : coordinateEuler V δ f = 0) (hh : coordinateEuler V δ ((Q₀ H) (Fin.last 3)) = 0) :
    coordinateEuler V δ (coordinateEuler V δ ((x₀) (Fin.last 3))) = 0 := by
  let U := coordinateEuler V δ
  obtain ⟨u, hu0, hNu, hUu⟩ :=
    original_directrix_output_constant_direction_constructs_constant_kernel p H hN hrank ht V f hV hfirst hf hh
  have hUt : U (p RatFunc.X) = 0 := by
    simp only [U, coordinateEuler_apply,
      (vertex_parameter_derivation_frame_parameter_values (D₀) (p RatFunc.X) ht).2,
      mul_zero, Finset.sum_const_zero]
  have hUV (i : Fin 3) : U (V i) = 0 := parameter_algebraic_coefficient_direction_constant p U hUt _ (hV i)
  have hUx (i : Fin 3) : U ((x₀) i.castSucc) = V i := coordinate_direction_coordinate δ
    (fun i : Fin 3 => (x₀) i.castSucc) V
    (vertex_parameter_derivation_frame_coordinate_values (D₀) (x₀)
      (algebraicPartial_coordinate F) (p RatFunc.X)).2.1 i
  have hUQ (i : Fin 4) : U ((Q₀ H) i) = 0 := by
    refine Fin.lastCases hh (fun i => ?_) i
    rw [hfirst, U.leibniz, hUV, hf]
    simp
  have hNux := algebraic_source_output_constant_derivation_coordinate_kernel H U hUQ
  obtain ⟨j, hj⟩ : ∃ j, V j ≠ 0 := by simpa only [ne_eq, funext_iff, Pi.zero_apply, not_forall] using hV0
  exact rank_three_constant_kernel_direction_forces_zero_acceleration (N₀ H)
    (algebraic_original_source_partials_jacobian_rank H hrank) U (x₀) u hNux hu0 hNu hUu
    j.castSucc (by rw [hUx]; exact hj) (by rw [hUx, hUV]) (Fin.last 3)

end DimensionFourDependence
