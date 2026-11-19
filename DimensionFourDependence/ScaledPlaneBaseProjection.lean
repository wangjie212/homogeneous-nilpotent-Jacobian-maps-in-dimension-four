import DimensionFourDependence.ScaledPlaneBasePower
import DimensionFourDependence.ScaledNormalPowerDirection
import DimensionFourDependence.IndependentGaussCoefficientRealization
import DimensionFourDependence.ClosedGaussAlgebraicRealization
import DimensionFourDependence.ClosedGaussNormalJetRealization

/-! # The actual scaled-plane base power forces constant projection

For a nonvertex generic base point, the actual scaled-plane congruence
constructs a nonzero fourth output, a nonzero vertex coefficient and
an original-field projected direction. The independent parameter field,
algebraic coefficient embedding, normal jets and polynomial descent are
all constructed. No proportional tangent restrictions or line-containment
hypothesis is supplied.
-/

namespace DimensionFourDependence

open MvPolynomial Matrix

universe u

set_option quotPrecheck false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 100000
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

variable {K : Type u} [Field K] [CharZero K] [IsAlgClosed K]
    (H : Fin 4 → MvPolynomial (Fin 4) K) (I : ImageRelationWitness H)
    (E : Type u) [Field E] [Algebra (closedGaussParameterField H I) E]
    [Algebra.IsAlgebraic (closedGaussParameterField H I) E]
    {d : ℕ} (hd : 0 < d) (hH : IsHomogMap H d) (hind : ¬ComponentsDependent H)
    (hGauss : gaussImageDimension H I = 1)
    (hvertex : rationalImageNormal H I.equation (Fin.last 3) = 0)
    (e : RatFunc K ≃ₐ[K] closedGaussParameterField H I)

local notation "S₀" => FractionRing (MvPolynomial (Fin 4) K)
local notation "ι" => extendedClosedGaussSourceCoefficientHom H I E
local notation "A₀" => extendedClosedGaussChosenRulingMatrix H I E hH hd hind hGauss
local notation "L₀" => linearFormPolynomial ((A₀) 0)
local notation "O" => extendedClosedGaussOutputLinearPolynomial H I E

include hvertex

/-- The constructed scaled-plane power congruence on the original
base gives constant projection from the fixed vertex at every nonvertex
generic base point. It also constructs the nonzero fourth output and
the nonzero value of the output form at the vertex. -/
theorem scaled_plane_base_power_constructs_constant_projection
    (p q : MvPolynomial (Fin 4) K) (hq : q ≠ 0) (hrel : IsRelPrime p q)
    (hparameter : closedGaussParameterSourceHom H I e RatFunc.X =
      algebraMap (MvPolynomial (Fin 4) K) S₀ p / algebraMap (MvPolynomial (Fin 4) K) S₀ q)
    (s : Fin 4 → E) (a : E) (ha : a ≠ 0)
    (hbase : (O) s - C (a ^ d) * (L₀) ^ d ∈
      Ideal.span ({MvPolynomial.map (ι) p, MvPolynomial.map (ι) q} :
        Set (MvPolynomial (Fin 4) E)))
    {F : Type*} [Field F] [Algebra K F]
    (x : Fin 4 → F) (hp : aeval x p = 0) (hq' : aeval x q = 0)
    (hx : (fun i : Fin 3 => x i.castSucc) ≠ 0) :
    s (Fin.last 3) ≠ 0 ∧ aeval x (H (Fin.last 3)) ≠ 0 ∧
      ∃ (c : F) (b : Fin 3 → K), c ≠ 0 ∧ b ≠ 0 ∧
        (fun i : Fin 3 => x i.castSucc) = c • (fun i => algebraMap K F (b i)) := by
  let G := AlgebraicClosure (RatFunc F)
  letI := independentParameterClosureAlgebra F
  letI := independentParameterClosureBaseAlgebra K F
  let : IsScalarTower K F G := independentParameterClosureScalarTower K F
  obtain ⟨φ, σ, ht, hσ, hσK, hcoeff⟩ :=
    algebraic_parameter_coefficients_construct_independent_realization K F (E := E) e
  let g : closedGaussParameterField H I →ₐ[K] G := φ.comp e.symm.toAlgHom
  let ψ : MvPolynomial (Fin 4) E →+* G :=
    MvPolynomial.eval₂Hom σ (fun i => algebraMap F G (x i))
  have hψC (b : E) : ψ (C b) = σ b := MvPolynomial.eval₂Hom_C _ _ _
  have hψX (i : Fin 4) : ψ (X i) = algebraMap F G (x i) := MvPolynomial.eval₂Hom_X' _ _ _
  have hcomp : ψ.comp (MvPolynomial.map (ι)) =
      (algebraMap F G).comp (aeval x).toRingHom := by
    apply MvPolynomial.ringHom_ext
    · intro b
      have hC : (aeval x).toRingHom (C b) = algebraMap K F b := aeval_C x b
      simp only [RingHom.comp_apply, MvPolynomial.map_C, hψC, hC]
      exact (hσK b).trans (IsScalarTower.algebraMap_apply K F G b)
    · intro i
      have hX : (aeval (R := K) x).toRingHom (X i) = x i := aeval_X x i
      simp only [RingHom.comp_apply, MvPolynomial.map_X, hψX, hX]
  have hpoly (P : MvPolynomial (Fin 4) K) :
      ψ (MvPolynomial.map (ι) P) = algebraMap F G (aeval x P) :=
    congrArg (fun f : MvPolynomial (Fin 4) K →+* G => f P) hcomp
  have hB : Ideal.span ({MvPolynomial.map (ι) p, MvPolynomial.map (ι) q} :
      Set (MvPolynomial (Fin 4) E)) ≤ RingHom.ker ψ := by
    apply Ideal.span_le.mpr
    intro P hP
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hP
    rcases hP with rfl | rfl
    · exact (hpoly p).trans (by rw [hp, map_zero])
    · exact (hpoly q).trans (by rw [hq', map_zero])
  have hsource : ψ ((O) s - C (a ^ d) * (L₀) ^ d) = 0 := hB hbase
  let w := closedGaussParameterNormal H I e
  have hw0 : w ≠ 0 := by
    intro hz
    have he := closedGaussParameterSourceHom_normal H I e (imageNormalPivot H I)
    change closedGaussParameterSourceHom H I e (w (imageNormalPivot H I)) = _ at he
    rw [hz, Pi.zero_apply, map_zero, div_self (imageNormalPivot_ne_zero H I)] at he
    exact zero_ne_one he
  have hwlast : w (Fin.last 3) = 0 := by
    apply (closedGaussParameterSourceHom H I e).injective
    change closedGaussParameterSourceHom H I e (w (Fin.last 3)) =
      closedGaussParameterSourceHom H I e 0
    rw [closedGaussParameterSourceHom_normal, hvertex, zero_div, map_zero]
  obtain ⟨v, hv, hprimitive, r, hr, hrep⟩ := rational_vector_primitive_polynomial_presentation w hw0
  have hvlast : v (Fin.last 3) = 0 := by
    rw [hrep] at hwlast
    have he := (mul_eq_zero.mp hwlast).resolve_left hr
    apply RatFunc.algebraMap_injective K
    simpa only [map_zero] using he
  obtain ⟨i, j, hminor, hLI⟩ :=
    closed_gauss_parameter_constructs_independent_normal_jet_minor H hd hH hind I hGauss e
  have hrow (i : Fin 4) : σ ((A₀) 0 i) = φ (w i) := by
    have he : (A₀) 0 i = algebraMap (closedGaussParameterField H I) E (e (w i)) := by
      change extendedClosedGaussRulingMatrix H I E
        (actualGaussRulingParameterChoice H I hH hd hind hGauss) 0 i = _
      rw [extendedClosedGaussRulingMatrix_first_row_closed_normal H I E e]
      rfl
    rw [he, hσ, e.symm_apply_apply]
  have hL : ψ (L₀) = ∑ i : Fin 3, φ (w i.castSucc) * algebraMap F G (x i.castSucc) := by
    simp only [linearFormPolynomial, map_sum, map_mul, hψC, hψX, hrow]
    rw [Fin.sum_univ_castSucc, hwlast, map_zero, zero_mul, add_zero]
  have hout (c : Fin 4 → E) : ψ ((O) c) =
      ∑ i : Fin 4, σ (c i) * algebraMap F G (aeval x (H i)) := by
    simp only [extendedClosedGaussOutputLinearPolynomial, MvPolynomial.smul_eq_C_mul,
      map_sum, map_mul, hψC, hpoly]
  have hfirst := original_fixed_vertex_pencil_base_output_first_three_zero
    H hd hH hind I hGauss hvertex e p q hq hrel hparameter (aeval x) hp hq'
  have hpower : σ (s (Fin.last 3)) * algebraMap F G (aeval x (H (Fin.last 3))) =
      (σ a) ^ d * (∑ i : Fin 3, φ (w i.castSucc) * algebraMap F G (x i.castSucc)) ^ d := by
    have he := hsource
    simp only [map_sub, map_mul, map_pow, hψC, hout, hL] at he
    rw [Fin.sum_univ_castSucc] at he
    simpa only [hfirst, map_zero, mul_zero, Finset.sum_const_zero, zero_add] using sub_eq_zero.mp he
  have hcoeff' : letI : Algebra (RatFunc K) G := φ.toRingHom.toAlgebra
      IsAlgebraic (RatFunc K) (σ (s (Fin.last 3))) ∧ IsAlgebraic (RatFunc K) (σ a) :=
    ⟨hcoeff _, hcoeff _⟩
  obtain ⟨hs, hH4, c, b, hc, hb, hdir⟩ :=
    scaled_normal_power_constructs_constant_projected_direction w v r hr hLI hrep hvlast φ ht
      (fun i : Fin 3 => x i.castSucc) hx (aeval x (H (Fin.last 3))) (σ (s (Fin.last 3)))
      (σ a) ((_root_.map_ne_zero σ).mpr ha) hcoeff' d hd hpower
  exact ⟨(_root_.map_ne_zero σ).mp hs, hH4, c, b, hc, hb, hdir⟩

end DimensionFourDependence
