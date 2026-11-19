import DimensionFourDependence.IndependentNormalPlaneIncidence
import DimensionFourDependence.HomogeneousPencilBaseExistence
import DimensionFourDependence.AffinePencilBaseRelations
import DimensionFourDependence.IndependentGaussCoefficientRealization
import DimensionFourDependence.NativeProportionalRootIdentities

/-! # The proportional-denominator root case is impossible for independent normals -/

namespace DimensionFourDependence

open MvPolynomial Matrix AlgebraicGeometry
open scoped TensorProduct

attribute [local instance] Algebra.TensorProduct.rightAlgebra

universe u

set_option quotPrecheck false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 100000
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

variable {K : Type u} [Field K] [CharZero K]
    (H : Fin 4 → MvPolynomial (Fin 4) K) (I : ImageRelationWitness H)
    (E : Type u) [Field E] [Algebra (closedGaussParameterField H I) E]
    [Algebra.IsAlgebraic (closedGaussParameterField H I) E]
    {d : ℕ} (hd : 0 < d) (hH : IsHomogMap H d) (hind : ¬ComponentsDependent H)
    (hGauss : gaussImageDimension H I = 1)
    (hNormal : LinearIndependent K (rationalImageNormal H I.equation))
    (e : RatFunc K ≃ₐ[K] closedGaussParameterField H I)

local notation "C₀" => closedGaussParameterField H I
local notation "S₀" => FractionRing (MvPolynomial (Fin 4) K)
local notation "T₀" => S₀ ⊗[C₀] E
local notation "F₀" => FractionRing T₀
local notation "xₐ" => extendedClosedGaussAffineTensorCoordinate H I E
local notation "ι" => extendedClosedGaussSourceCoefficientHom H I E
local notation "A₀" => extendedClosedGaussChosenRulingMatrix H I E hH hd hind hGauss
local notation "L₀" => linearFormPolynomial ((A₀) 0)
local notation "O" => extendedClosedGaussOutputLinearPolynomial H I E
local notation "N" => extendedClosedGaussNormalizationScheme H I E hH e
local notation "w₀" => extendedClosedGaussNormalizationHyperplaneWeight H I E hH e
local notation "R" => rulingFormRestriction (LinearMap.ker (A₀).toLin')

local instance independentNormalScaledPowerDomain : IsDomain T₀ :=
  (actual_closed_gauss_cover_algebraic_base_change_isField H I E).isDomain
local instance independentNormalScaledPowerIntegral : IsIntegral N :=
  extendedClosedGaussNormalizationScheme_isIntegral H I E hH e
noncomputable local instance independentNormalScaledPowerAlgebra : Algebra E (N).functionField :=
  extendedClosedGaussOwnFunctionFieldAlgebra H I E hH e

include hNormal e

/-- A nonzero original pencil-base point cannot satisfy the actual
scaled-plane power congruence when the four original normal coordinates
are independent. The parameter is realized independently of that point. -/
theorem independent_normal_scaled_plane_base_power_impossible
    (p q : MvPolynomial (Fin 4) K) (hq : q ≠ 0) (hrel : IsRelPrime p q)
    (hparameter : closedGaussParameterSourceHom H I e RatFunc.X =
      algebraMap (MvPolynomial (Fin 4) K) S₀ p / algebraMap (MvPolynomial (Fin 4) K) S₀ q)
    (s : Fin 4 → E) (a : E) (ha : a ≠ 0)
    (hbase : (O) s - C (a ^ d) * (L₀) ^ d ∈
      Ideal.span ({MvPolynomial.map (ι) p, MvPolynomial.map (ι) q} :
        Set (MvPolynomial (Fin 4) E)))
    {F : Type*} [Field F] [Algebra K F]
    (x : Fin 4 → F) (hp : aeval x p = 0) (hq' : aeval x q = 0) (hx : x ≠ 0) : False := by
  let G := AlgebraicClosure (RatFunc F)
  letI := independentParameterClosureAlgebra F
  letI := independentParameterClosureBaseAlgebra K F
  let : IsScalarTower K F G := independentParameterClosureScalarTower K F
  obtain ⟨φ, σ, ht, hσ, hσK, _hcoeff⟩ :=
    algebraic_parameter_coefficients_construct_independent_realization K F (E := E) e
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
      have hX : (aeval («R» := K) x).toRingHom (X i) = x i := aeval_X x i
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
  have hout0 : ψ ((O) s) = 0 := by
    have hzero := original_independent_normal_pencil_base_outputs_zero
      H hd hH I hNormal e p q hq hrel hparameter (aeval x) hp hq'
    simp only [extendedClosedGaussOutputLinearPolynomial, MvPolynomial.smul_eq_C_mul,
      map_sum, map_mul, hψC, hpoly, hzero, map_zero, mul_zero, Finset.sum_const_zero]
  have hsource : ψ ((O) s - C (a ^ d) * (L₀) ^ d) = 0 := hB hbase
  have hpower : (σ a) ^ d * (ψ (L₀)) ^ d = 0 := by
    simpa only [map_sub, hout0, map_mul, hψC, map_pow, zero_sub, neg_eq_zero] using hsource
  have hL : ψ (L₀) = 0 := by
    have he := (mul_eq_zero.mp hpower).resolve_left (pow_ne_zero d ((map_ne_zero σ).mpr ha))
    by_contra hne
    exact pow_ne_zero d hne he
  let w := closedGaussParameterNormal H I e
  have hrow (i : Fin 4) : σ ((A₀) 0 i) = φ (w i) := by
    have he : (A₀) 0 i = algebraMap C₀ E (e (w i)) := by
      change extendedClosedGaussRulingMatrix H I E
        (actualGaussRulingParameterChoice H I hH hd hind hGauss) 0 i = _
      rw [extendedClosedGaussRulingMatrix_first_row_closed_normal H I E e]
      rfl
    rw [he, hσ, e.symm_apply_apply]
  have hplane : ∑ i, φ (w i) * algebraMap F G (x i) = 0 := by
    simpa only [linearFormPolynomial, map_sum, map_mul, hψC, hψX, hrow] using hL
  have hw : LinearIndependent K w := by
    let f := closedGaussParameterSourceHom H I e
    let c := rationalImageNormal H I.equation (imageNormalPivot H I)
    apply LinearIndependent.of_comp (c • f.toLinearMap)
    convert hNormal using 1
    funext i
    change c * f (w i) = rationalImageNormal H I.equation i
    rw [closedGaussParameterSourceHom_normal, mul_div_cancel₀ _ (imageNormalPivot_ne_zero H I)]
  exact hx (independent_rational_normal_transcendental_incidence_forces_zero w hw φ ht x hplane)

/-- The original map constructs its own nonzero pencil-base point,
so no actual affine source scaled-plane power can occur for independent normals. -/
theorem no_actual_affine_scaled_plane_power_for_independent_normal
    (s : Fin 4 → E) (a : E) (ha : a ≠ 0)
    (hpower : aeval (xₐ) ((O) s) = algebraMap E F₀ (a ^ d) * (aeval (xₐ) (L₀)) ^ d) : False := by
  obtain ⟨p, q, D, Q, _hD, _hp0, hq0, _hp, _hq, hrel, hparameter, hQ, _hheight, i, hi⟩ :=
    actual_closed_gauss_parameter_constructs_nonempty_base_component H hH I e
  let : Q.IsPrime := hQ.isPrime
  let x := primeQuotientCoordinate Q
  have hp : aeval x p = 0 := by
    change p ∈ fiberVanishingIdeal (L := K) x
    rw [primeQuotientCoordinate_relations]
    exact hQ.le (Ideal.subset_span (by simp))
  have hq : aeval x q = 0 := by
    change q ∈ fiberVanishingIdeal (L := K) x
    rw [primeQuotientCoordinate_relations]
    exact hQ.le (Ideal.subset_span (by simp))
  have hx : x ≠ 0 := by
    intro hz
    have hmem : X i.castSucc ∈ fiberVanishingIdeal (L := K) x := by
      change aeval x (X i.castSucc) = 0
      rw [aeval_X, hz]
      rfl
    rw [primeQuotientCoordinate_relations] at hmem
    exact hi hmem
  have hbase : (O) s - C (a ^ d) * (L₀) ^ d ∈
      Ideal.span ({MvPolynomial.map (ι) p, MvPolynomial.map (ι) q} :
        Set (MvPolynomial (Fin 4) E)) := by
    apply affine_tensor_relation_mem_pencil_base_ideal H I E e p q hq0 hrel hparameter
    simpa only [map_sub, map_mul, map_pow, aeval_C, sub_eq_zero] using hpower
  exact independent_normal_scaled_plane_base_power_impossible
    H I E hd hH hind hGauss hNormal e p q hq0 hrel hparameter s a ha hbase x hp hq hx

/-- The same exclusion holds for the actual normalized source value;
the homogeneous native relation is transported to the actual affine tensor. -/
theorem no_actual_native_scaled_plane_power_for_independent_normal
    (s : Fin 4 → E) (a : E) (ha : a ≠ 0)
    (hpower : aeval (w₀) ((O) s) =
      algebraMap E (N).functionField (a ^ d) * (aeval (w₀) (L₀)) ^ d) : False := by
  have hhom : ((O) s - C (a ^ d) * (L₀) ^ d).IsHomogeneous d := by
    apply (extendedClosedGaussOutputLinearPolynomial_homogeneous H I E hH s).sub
    simpa only [Nat.one_mul] using ((linearFormPolynomial_homogeneous
      (extendedClosedGaussChosenRulingMatrix H I E hH hd hind hGauss 0)).pow d).C_mul (a ^ d)
  have hn : aeval (w₀) ((O) s - C (a ^ d) * (L₀) ^ d) = 0 := by
    simpa only [map_sub, map_mul, map_pow, aeval_C, sub_eq_zero] using hpower
  have haff := (extendedClosedGauss_affine_tensor_native_homogeneous_zero_iff H I E hH e
    ((O) s - C (a ^ d) * (L₀) ^ d) hhom).mpr hn
  apply no_actual_affine_scaled_plane_power_for_independent_normal H I E hd hH hind hGauss hNormal e s a ha
  simpa only [map_sub, map_mul, map_pow, aeval_C, sub_eq_zero] using haff

/-- The proportional m,n branch is impossible for a map with four
independent actual normal coordinates. No base point or base power is supplied. -/
theorem no_actual_proportional_root_denominator_for_independent_normal
    (cS cM cN : Fin 4 → E) (r : (N).functionField) (hr : r ≠ 0)
    (hroot : r ^ d = aeval (w₀) ((O) cS))
    (γ : E) (hγ : γ ≠ 0) (hMN : (R) cM = γ • (R) cN)
    (hformula : r = aeval (w₀) ((O) cN) *
      (∑ i, algebraMap E (N).functionField ((A₀) 0 i) * (w₀) i) / aeval (w₀) ((O) cM)) : False := by
  have he := native_proportional_denominator_source_power
    H I E hH e hd hind hGauss cS cM cN r hr hroot γ hγ hMN hformula
  apply no_actual_native_scaled_plane_power_for_independent_normal
    H I E hd hH hind hGauss hNormal e cS γ⁻¹ (inv_ne_zero hγ)
  simpa only [map_pow, linearFormPolynomial, map_sum, map_mul, aeval_C, aeval_X] using he

end DimensionFourDependence
