import DimensionFourDependence.ClosedGaussNormalJetRealization
import DimensionFourDependence.RankThreeDerivationKernel
import DimensionFourDependence.RealizedConeNormalIncidence

/-! # The original closed Gauss realization constructs the cone's direction incidences -/

namespace DimensionFourDependence

open MvPolynomial Matrix

set_option quotPrecheck false
set_option maxHeartbeats 5000000
set_option synthInstance.maxHeartbeats 100000
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

variable {K F : Type*} [Field K] [CharZero K] [Field F] [Algebra K F]
    [Algebra (FractionRing (MvPolynomial (Fin 4) K)) F]
    [IsScalarTower K (FractionRing (MvPolynomial (Fin 4) K)) F]
    [Algebra.IsAlgebraic (FractionRing (MvPolynomial (Fin 4) K)) F]
    (H : Fin 4 → MvPolynomial (Fin 4) K) (I : ImageRelationWitness H)
    (e : RatFunc K ≃ₐ[K] closedGaussParameterField H I)

local notation "S₀" => FractionRing (MvPolynomial (Fin 4) K)
local notation "x₀" => fun i : Fin 4 => algebraMap S₀ F (rationalCoordinate (K := K) i)
local notation "p₀" => (IsScalarTower.toAlgHom K S₀ F).comp (closedGaussParameterSourceHom H I e)
local notation "ν₀" => fun i : Fin 3 => (p₀) (closedGaussParameterNormal H I e i.castSucc)

/-- Every actual first-three-coordinate cone presentation has the
constructed closed normal and its first parameter derivative as
annihilators. The direction need not be the normalized directrix used
in the construction, and neither incidence is supplied. -/
theorem actual_closed_cone_presentation_constructs_directrix_normal_incidences
    {d : ℕ} (hd : 0 < d) (hH : IsHomogMap H d) (hind : ¬ ComponentsDependent H)
    (hGauss : gaussImageDimension H I = 1)
    (hvertex : rationalImageNormal H I.equation (Fin.last 3) = 0)
    (T : Derivation K F F) (hT : T ((p₀) RatFunc.X) = 1)
    (V : Fin 3 → F) (r : F) (hr : r ≠ 0)
    (hfirst : ∀ i : Fin 3, algebraMap S₀ F (algebraMap (MvPolynomial (Fin 4) K) S₀ (H i.castSucc)) = V i * r ^ d) :
    (ν₀) ⬝ᵥ V = 0 ∧ (fun i => T ((ν₀) i)) ⬝ᵥ V = 0 := by
  obtain ⟨V₀, j, _hVj, _hHj, _hLI, hvalues, hnormal, hderivative, _htangent⟩ :=
    closed_fixed_vertex_cone_constructs_rational_scalar_direction H hd hH hind I hGauss hvertex e
  have hvaluesF (i : Fin 3) :
      algebraMap S₀ F (algebraMap (MvPolynomial (Fin 4) K) S₀ (H i.castSucc)) =
        (p₀) (V₀ i) * algebraMap S₀ F (algebraMap (MvPolynomial (Fin 4) K) S₀ (H j.castSucc)) := by
    change algebraMap S₀ F (algebraMap (MvPolynomial (Fin 4) K) S₀ (H i.castSucc)) =
      algebraMap S₀ F (closedGaussParameterSourceHom H I e (V₀ i)) *
        algebraMap S₀ F (algebraMap (MvPolynomial (Fin 4) K) S₀ (H j.castSucc))
    simpa only [map_mul] using congrArg (algebraMap S₀ F) (hvalues i)
  have hVi (i : Fin 3) : V i = (p₀) (V₀ i) * V j := by
    apply mul_right_cancel₀ (pow_ne_zero d hr)
    rw [← hfirst i, hvaluesF, hfirst j]
    ring
  have hpair (ζ : Fin 3 → RatFunc K) (hζ : ζ ⬝ᵥ V₀ = 0) :
      (fun i => (p₀) (ζ i)) ⬝ᵥ V = 0 := by
    calc
      _ = (p₀) (ζ ⬝ᵥ V₀) * V j := by
        simp only [dotProduct, map_sum, map_mul, Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro i _hi
        rw [hVi i]
        ring
      _ = 0 := by rw [hζ, map_zero, zero_mul]
  have hTν (i : Fin 3) : T ((ν₀) i) =
      (p₀) (rationalParameterDerivative K (closedGaussParameterNormal H I e i.castSucc)) := by
    rw [rational_parameter_chain_rule, hT, mul_one]
  exact ⟨hpair _ hnormal, by simpa only [hTν] using hpair _ hderivative⟩

/-- The original nilpotent rank-three matrix makes the actual
closed fixed-vertex normal annihilate every output-constant derivation's
projected source direction. No separate geometric incidence is supplied. -/
theorem actual_closed_fixed_vertex_output_constant_derivation_normal_pairing
    (hN : IsNilpotent (jac H)) (hrank : polyRank (jac H) = 3)
    (hvertex : rationalImageNormal H I.equation (Fin.last 3) = 0)
    (D : Derivation K F F)
    (hDQ : ∀ i : Fin 4, D (algebraMap S₀ F (algebraMap (MvPolynomial (Fin 4) K) S₀ (H i))) = 0) :
    (ν₀) ⬝ᵥ (fun i : Fin 3 => D ((x₀) i.castSucc)) = 0 := by
  let f : S₀ →ₐ[K] F := IsScalarTower.toAlgHom K S₀ F
  have hkernel := algebraic_source_output_constant_derivation_coordinate_kernel H D hDQ
  rw [algebraic_original_source_partials_polynomial_jacobian] at hkernel
  change ((jac H).map (algebraMap (MvPolynomial (Fin 4) K) S₀)).map f.toRingHom *ᵥ
    (fun i => D ((x₀) i)) = 0 at hkernel
  have he := realized_nilpotent_image_normal_kernel_pairing H hN hrank I f _ hkernel
  have hνvalue (i : Fin 4) : (p₀) (closedGaussParameterNormal H I e i) =
      f (rationalImageNormal H I.equation i / rationalImageNormal H I.equation (imageNormalPivot H I)) :=
    congrArg (algebraMap S₀ F) (closedGaussParameterSourceHom_normal H I e i)
  have hlast : f (rationalImageNormal H I.equation (Fin.last 3) /
      rationalImageNormal H I.equation (imageNormalPivot H I)) = 0 := by
    rw [hvertex, zero_div, map_zero]
  simp only [dotProduct] at he ⊢
  rw [Fin.sum_univ_castSucc, hlast, zero_mul, add_zero] at he
  simpa only [← hνvalue] using he

end DimensionFourDependence
