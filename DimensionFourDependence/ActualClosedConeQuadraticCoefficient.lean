import DimensionFourDependence.RankThreeActualParabolicCone
import DimensionFourDependence.ClosedConeSourceIncidences
import DimensionFourDependence.ParameterAlgebraicFieldReflection

/-! # The original closed fixed-vertex cone constructs its actual nonzero quadratic numerator

The projected fiber direction's independence from the directrix and its
parameter algebraicity remain explicit. The original Gauss curve,
Jacobian and actual fiber equations construct every normal incidence,
jet, tangent decomposition, nonzero directrix derivative and acceleration
needed for the quadratic numerator, in the same geometric constants.
-/

namespace DimensionFourDependence

open MvPolynomial Matrix

set_option quotPrecheck false
set_option maxHeartbeats 6000000
set_option synthInstance.maxHeartbeats 100000
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

/-- An actual field embedding preserves independence of two
ternary directions, over the entire target field. -/
theorem independent_ternary_pair_map_fieldHom
    {E F : Type*} [Field E] [Field F] (f : E →+* F) (V A : Fin 3 → E)
    (hVA : LinearIndependent E ![V, A]) :
    LinearIndependent F ![(fun i => f (V i)), (fun i => f (A i))] := by
  apply crossProduct_ne_zero_iff_linearIndependent.mp
  rw [← crossProduct_map_fieldHom f V A]
  intro hz
  apply (crossProduct_ne_zero_iff_linearIndependent.mpr hVA)
  funext i
  apply f.injective
  simpa only [Pi.zero_apply, map_zero] using congrFun hz i

variable {K E F : Type*} [Field K] [CharZero K] [Field E] [Field F] [CharZero F]
    [Algebra K E] [Algebra K F] [Algebra E F] [IsScalarTower K E F]
    [Algebra (FractionRing (MvPolynomial (Fin 4) K)) F]
    [IsScalarTower K (FractionRing (MvPolynomial (Fin 4) K)) F]
    [Algebra.IsAlgebraic (FractionRing (MvPolynomial (Fin 4) K)) F]
    (H : Fin 4 → MvPolynomial (Fin 4) K) (I : ImageRelationWitness H)
    (e : RatFunc K ≃ₐ[K] closedGaussParameterField H I)
    (g : closedGaussParameterField H I →ₐ[K] E)
    (hg : ∀ c : closedGaussParameterField H I, algebraMap E F (g c) =
      algebraMap (FractionRing (MvPolynomial (Fin 4) K)) F
        (c : FractionRing (MvPolynomial (Fin 4) K)))

local notation "S₀" => FractionRing (MvPolynomial (Fin 4) K)
local notation "x₀" => fun i : Fin 4 => algebraMap S₀ F (rationalCoordinate (K := K) i)
local notation "D₀" => algebraicPartial (K := K) F
local notation "p₀" => (IsScalarTower.toAlgHom K S₀ F).comp (closedGaussParameterSourceHom H I e)
local notation "ν₀" => fun i : Fin 3 => (p₀) (closedGaussParameterNormal H I e i.castSucc)
local notation "L₀" => (ν₀) ⬝ᵥ (fun i : Fin 3 => (x₀) i.castSucc)

include hg

/-- On the independent-direction branch of the actual original
closed fixed-vertex cone, the original map and fiber equations construct
C != 0 and kappa != 0 in the same geometric constants, algebraic over
the same realized closed Gauss field, with C = kappa/R. Normal jets,
normal-direction incidences, alpha,beta, nonzero f_V and all directional
derivative conditions are derived instead of supplied. -/
theorem actual_closed_fixed_vertex_cone_constructs_quadratic_numerator
    {d : ℕ} (hd : 0 < d) (hH : IsHomogMap H d) (hN : IsNilpotent (jac H))
    (hrank : polyRank (jac H) = 3) (hind : ¬ ComponentsDependent H)
    (hGauss : gaussImageDimension H I = 1)
    (hvertex : rationalImageNormal H I.equation (Fin.last 3) = 0)
    (hsourcevertex : rationalPartial (K := K) (Fin.last 3)
      (closedGaussParameterSourceHom H I e RatFunc.X) ≠ 0)
    (t : F) (htrans : Transcendental E t) (x A V : Fin 3 → E) (w B C R y a b : E)
    (hline : ∀ i : Fin 3, (x₀) i.castSucc = algebraMap E F (x i) + algebraMap E F (A i) * t)
    (hparabola : (x₀) (Fin.last 3) = algebraMap E F w + algebraMap E F B * t + algebraMap E F C * t ^ 2)
    (hy : algebraMap S₀ F (algebraMap (MvPolynomial (Fin 4) K) S₀ (H (Fin.last 3))) = algebraMap E F y)
    (hR : R ≠ 0) (hb0 : b ≠ 0)
    (hfirst : ∀ i : Fin 3, algebraMap S₀ F (algebraMap (MvPolynomial (Fin 4) K) S₀ (H i.castSucc)) =
      algebraMap E F (V i) * (algebraMap E F R) ^ d)
    (hlast : algebraMap S₀ F (algebraMap (MvPolynomial (Fin 4) K) S₀ (H (Fin.last 3))) =
      algebraMap E F a * (algebraMap E F R) ^ d + algebraMap E F b * (algebraMap E F R) ^ (d - 1) * (L₀))
    (hV : ∀ i, IsAlgebraic g.fieldRange (V i)) (hA : ∀ i, IsAlgebraic g.fieldRange (A i))
    (ha : IsAlgebraic g.fieldRange a) (hb : IsAlgebraic g.fieldRange b)
    (hVA : LinearIndependent E ![V, A]) :
    C ≠ 0 ∧ ∃ κ : E, κ ≠ 0 ∧ IsAlgebraic g.fieldRange κ ∧ C = κ / R := by
  obtain ⟨hp, ht⟩ := compatible_closed_parameter_constructs_constant_value_and_nonzero_vertex_partial
    H I e g hg hsourcevertex
  let T := vertexParameterPartial (D₀) ((p₀) RatFunc.X)
  have hT : T ((p₀) RatFunc.X) = 1 :=
    (vertex_parameter_derivation_frame_parameter_values (D₀) ((p₀) RatFunc.X) ht).1
  have halg (c : E) (hc : IsAlgebraic g.fieldRange c) : IsAlgebraic (p₀).fieldRange (algebraMap E F c) :=
    compatible_closed_parameter_coefficient_image_isAlgebraic H I e g hg c hc
  have hνalg (i : Fin 3) : IsAlgebraic (p₀).fieldRange ((ν₀) i) :=
    isAlgebraic_algebraMap (R := (p₀).fieldRange) (A := F)
      ((p₀).equivFieldRange (closedGaussParameterNormal H I e i.castSucc))
  obtain ⟨hνV, hν₁V⟩ := actual_closed_cone_presentation_constructs_directrix_normal_incidences
    H I e hd hH hind hGauss hvertex T hT (fun i => algebraMap E F (V i)) (algebraMap E F R)
      (by simpa only [map_zero] using (algebraMap E F).injective.ne hR) hfirst
  obtain ⟨D, hconst, _hDt, hDx, _hframe, _hDw, _hacc⟩ :=
    actual_parabolic_source_constructs_transverse_frame_derivation (p₀) hp ht t htrans x A w B C hline hparabola
  have hDQ (i : Fin 4) : D (algebraMap S₀ F (algebraMap (MvPolynomial (Fin 4) K) S₀ (H i))) = 0 := by
    refine Fin.lastCases ?_ (fun i => ?_) i
    · rw [hy, hconst]
    · rw [hfirst, D.leibniz, hconst]
      simp only [Derivation.leibniz_pow, hconst, smul_eq_mul, mul_zero, zero_mul, nsmul_zero, zero_add]
  have hνA : (ν₀) ⬝ᵥ (fun i => algebraMap E F (A i)) = 0 := by
    simpa only [hDx] using actual_closed_fixed_vertex_output_constant_derivation_normal_pairing
      H I e hN hrank hvertex D hDQ
  have hjet := realized_closed_gauss_fixed_vertex_normal_jets_independent
    H hd hH hind I hGauss hvertex e (p₀) T hT
  have hVAmap := independent_ternary_pair_map_fieldHom (algebraMap E F) V A hVA
  obtain ⟨hC0, κ, hκ, hκalg, hC⟩ := actual_parabolic_rank_three_cone_constructs_constant_quadratic_numerator
    (p₀) H hN hrank hp ht t htrans x A w B C R y hline hparabola hy hd
    (fun i => algebraMap E F (V i)) (ν₀) (algebraMap E F a) (algebraMap E F b) (L₀)
    hR (by simpa only [map_zero] using (algebraMap E F).injective.ne hb0) hfirst hlast
    (fun i => halg _ (hV i)) hνalg (halg a ha) (halg b hb) (fun i => halg _ (hA i))
    rfl hνV hν₁V hνA hjet hVAmap
  exact ⟨hC0, κ, hκ,
    (compatible_closed_parameter_coefficient_image_isAlgebraic_iff H I e g hg κ).mp hκalg, hC⟩

end DimensionFourDependence
