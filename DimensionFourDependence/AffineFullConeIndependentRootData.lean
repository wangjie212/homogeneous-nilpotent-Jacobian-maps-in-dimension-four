import DimensionFourDependence.ExtendedFullConeRootForms
import DimensionFourDependence.AffineSourceConeForm
import DimensionFourDependence.FixedVertexRootNumerator
import DimensionFourDependence.HomogeneousRationalRootTransfer

/-! # The actual affine full cone supplies independent native root forms -/

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
    {d : ℕ} (hH : IsHomogMap H d) (e : RatFunc K ≃ₐ[K] closedGaussParameterField H I)
    (hd : 0 < d) (hind : ¬ComponentsDependent H) (hGauss : gaussImageDimension H I = 1)

local notation "C₀" => closedGaussParameterField H I
local notation "S₀" => FractionRing (MvPolynomial (Fin 4) K)
local notation "T₀" => S₀ ⊗[C₀] E
local notation "F₀" => FractionRing T₀
local notation "xₐ" => extendedClosedGaussAffineTensorCoordinate H I E
local notation "A₀" => extendedClosedGaussChosenRulingMatrix H I E hH hd hind hGauss
local notation "W₀" => LinearMap.ker (A₀).toLin'
local notation "O" => extendedClosedGaussOutputLinearPolynomial H I E
local notation "L₀" => linearFormPolynomial ((A₀) 0)
local notation "N₀" => extendedClosedGaussNormalizationScheme H I E hH e
local notation "w" => extendedClosedGaussNormalizationHyperplaneWeight H I E hH e

local instance affineFullConeIndependentRootDataDomain : IsDomain T₀ :=
  (actual_closed_gauss_cover_algebraic_base_change_isField H I E).isDomain
local instance affineFullConeIndependentRootDataIntegral : IsIntegral N₀ :=
  extendedClosedGaussNormalizationScheme_isIntegral H I E hH e
noncomputable local instance affineFullConeIndependentRootDataAlgebra : Algebra E (N₀).functionField :=
  extendedClosedGaussOwnFunctionFieldAlgebra H I E hH e

/-- The exact original numerator is an index of the constructed
independent root data, so later graph transfer retains its chart. -/
noncomputable def ActualChosenIndependentGaussRootDataForNumerator (cN : Fin 4 → E) : Prop :=
  ∃ (cS cM : Fin 4 → E) (r : (N₀).functionField),
    cM (Fin.last 3) ≠ 0 ∧ cS (Fin.last 3) = 0 ∧ r ≠ 0 ∧
      r ^ d = aeval (w) ((O) cS) ∧ aeval (w) ((O) cM) ≠ 0 ∧
      r = aeval (w) ((O) cN) * aeval (w) (L₀) / aeval (w) ((O) cM) ∧
      HasActualGaussRootNumerator H I E e cN ∧
      LinearIndependent E ![rulingFormRestriction (W₀) cM, rulingFormRestriction (W₀) cS]

/-- Independent root forms in the original finite coefficient field,
with exact native root formula and original numerator provenance.
The power form vanishes at the fourth axis, and the denominator form
does not; these are constructed properties of the same witnesses. -/
noncomputable def ActualChosenIndependentGaussRootData : Prop :=
  ∃ (cS cM cN : Fin 4 → E) (r : (N₀).functionField),
    cM (Fin.last 3) ≠ 0 ∧ cS (Fin.last 3) = 0 ∧ r ≠ 0 ∧
      r ^ d = aeval (w) ((O) cS) ∧ aeval (w) ((O) cM) ≠ 0 ∧
      r = aeval (w) ((O) cN) * aeval (w) (L₀) / aeval (w) ((O) cM) ∧
      HasActualGaussRootNumerator H I E e cN ∧
      LinearIndependent E ![rulingFormRestriction (W₀) cM, rulingFormRestriction (W₀) cS]

/-- The actual full affine cone formula constructs independent
native ruling root data over exactly the same coefficient field.
Its original nonzero numerator and normal level are retained. -/
theorem actual_affine_full_cone_constructs_independent_native_root_data_retaining_numerator
    (hvertex : rationalImageNormal H I.equation (Fin.last 3) = 0)
    (cN : Fin 4 → E) (hN : HasActualGaussRootNumerator H I E e cN)
    (hn : aeval (w) ((O) cN) ≠ 0) (hL : aeval (w) (L₀) ≠ 0)
    (r : F₀) (hr : r ≠ 0)
    (hcone : AffineSourceFixedVertexConeRootForm H I E hH hd hind hGauss r) :
    ActualChosenIndependentGaussRootDataForNumerator H I E hH e hd hind hGauss cN := by
  classical
  let y : Fin 4 → F₀ := fun i => aeval (xₐ)
    (MvPolynomial.map (extendedClosedGaussSourceCoefficientHom H I E) (H i))
  let ell : F₀ := ∑ i : Fin 3, algebraMap E F₀ ((A₀) 0 i.castSucc) * (xₐ) i.castSucc
  have hcol (q : Fin 2) : (A₀) q (Fin.last 3) = 0 :=
    extended_chosen_ruling_fixed_vertex_last_column H I E hH hd hind hGauss hvertex q
  have haxis : (A₀) *ᵥ (Fin.snoc (0 : Fin 3 → E) 1 : Fin 4 → E) = 0 := by
    funext q
    change (∑ i : Fin 4, (A₀) q i * (Fin.snoc (0 : Fin 3 → E) 1 : Fin 4 → E) i) = 0
    rw [Fin.sum_univ_castSucc]
    change (∑ i : Fin 3, (A₀) q i.castSucc * (Fin.snoc (0 : Fin 3 → E) 1 : Fin 4 → E) i.castSucc) +
      (A₀) q (Fin.last 3) * (Fin.snoc (0 : Fin 3 → E) 1 : Fin 4 → E) (Fin.last 3) = 0
    simp only [Fin.snoc_castSucc, Pi.zero_apply, mul_zero, Finset.sum_const_zero, Fin.snoc_last,
      mul_one, zero_add, hcol]
  have hO (c : Fin 4 → E) : aeval (xₐ) ((O) c) = (fun i => algebraMap E F₀ (c i)) ⬝ᵥ y := by
    simp only [extendedClosedGaussOutputLinearPolynomial, MvPolynomial.smul_eq_C_mul,
      map_sum, map_mul, aeval_C, dotProduct, y]
  have hLa : aeval (xₐ) (L₀) = ell := by
    simp only [linearFormPolynomial, map_sum, map_mul, aeval_C, aeval_X]
    rw [Fin.sum_univ_castSucc]
    change (∑ i : Fin 3, algebraMap E F₀ ((A₀) 0 i.castSucc) * (xₐ) i.castSucc) +
      algebraMap E F₀ ((A₀) 0 (Fin.last 3)) * (xₐ) (Fin.last 3) = ell
    rw [hcol, map_zero, zero_mul, add_zero]
  have hnA : aeval (xₐ) ((O) cN) ≠ 0 := by
    intro hz
    exact hn ((extendedClosedGauss_affine_tensor_native_homogeneous_zero_iff H I E hH e _
      (extendedClosedGaussOutputLinearPolynomial_homogeneous H I E hH cN)).mp hz)
  have hLA : aeval (xₐ) (L₀) ≠ 0 := by
    intro hz
    exact hL ((extendedClosedGauss_affine_tensor_native_homogeneous_zero_iff H I E hH e _
      (linearFormPolynomial_homogeneous _)).mp hz)
  obtain ⟨V, a, b, hV, hb, hinc, hfirst, hlast⟩ := hcone
  have hy : (A₀).map (algebraMap E F₀) *ᵥ y = 0 := by
    funext q
    change (∑ i : Fin 4, algebraMap E F₀ ((A₀) q i) * y i) = 0
    rw [Fin.sum_univ_castSucc]
    change (∑ i : Fin 3, algebraMap E F₀ ((A₀) q i.castSucc) * y i.castSucc) +
      algebraMap E F₀ ((A₀) q (Fin.last 3)) * y (Fin.last 3) = 0
    rw [hcol, map_zero, zero_mul, add_zero]
    have he : (∑ i : Fin 3, algebraMap E F₀ ((A₀) q i.castSucc) * y i.castSucc) =
        algebraMap E F₀ (∑ i : Fin 3, (A₀) q i.castSucc * V i) * r ^ d := by
      simp only [map_sum, map_mul, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro i _
      rw [show y i.castSucc = algebraMap E F₀ (V i) * r ^ d from hfirst i]
      ring
    rw [he, hinc, map_zero, zero_mul]
  obtain ⟨M, S, hMlast, hSlast, hprod, hpower, hpair⟩ :=
    extended_full_cone_constructs_root_forms_over_same_coefficients (A₀) y hy haxis hd r hr V hV a b ell hb
      hfirst hlast cN (actual_gauss_root_numerator_fixed_vertex_coordinate_zero H I E e hH hd hind hGauss hvertex cN hN)
      (by rw [← hO]; exact hnA)
  rw [← hO, ← hO, ← hLa] at hprod
  rw [← hO] at hpower
  have hmA : aeval (xₐ) ((O) M) ≠ 0 := by
    intro hz
    rw [hz, zero_mul] at hprod
    exact (mul_ne_zero hnA hLA) hprod.symm
  have hformula : r = aeval (xₐ) ((O) cN) * aeval (xₐ) (L₀) / aeval (xₐ) ((O) M) := by
    apply (eq_div_iff hmA).mpr
    exact (mul_comm _ _).trans hprod
  have hmNative : aeval (w) ((O) M) ≠ 0 := by
    intro hz
    exact hmA ((extendedClosedGauss_affine_tensor_native_homogeneous_zero_iff H I E hH e _
      (extendedClosedGaussOutputLinearPolynomial_homogeneous H I E hH M)).mpr hz)
  let rNative := aeval (w) ((O) cN) * aeval (w) (L₀) / aeval (w) ((O) M)
  have hpowerNative : rNative ^ d = aeval (w) ((O) S) :=
    homogeneous_relations_transfer_rational_root_power ((O) cN) ((O) M) ((O) S) (L₀)
      (extendedClosedGaussOutputLinearPolynomial_homogeneous H I E hH cN)
      (extendedClosedGaussOutputLinearPolynomial_homogeneous H I E hH M)
      (extendedClosedGaussOutputLinearPolynomial_homogeneous H I E hH S)
      (linearFormPolynomial_homogeneous _) (xₐ) (w)
      (fun P _ hP => extendedClosedGauss_affine_tensor_native_homogeneous_zero_iff H I E hH e P hP)
      r hmA hformula hpower.symm
  exact ⟨S, M, rNative, hMlast, hSlast, div_ne_zero (mul_ne_zero hn hL) hmNative,
    hpowerNative, hmNative, rfl, hN, hpair⟩

/-- Forgetting only the numerator index recovers the original
existential form of the independent root data. -/
theorem actual_affine_full_cone_constructs_independent_native_root_data
    (hvertex : rationalImageNormal H I.equation (Fin.last 3) = 0)
    (cN : Fin 4 → E) (hN : HasActualGaussRootNumerator H I E e cN)
    (hn : aeval (w) ((O) cN) ≠ 0) (hL : aeval (w) (L₀) ≠ 0)
    (r : F₀) (hr : r ≠ 0)
    (hcone : AffineSourceFixedVertexConeRootForm H I E hH hd hind hGauss r) :
    ActualChosenIndependentGaussRootData H I E hH e hd hind hGauss := by
  obtain ⟨S, M, rNative, hMlast, hSlast, hrNative, hpower, hmNative, hformula, hnumerator, hpair⟩ :=
    actual_affine_full_cone_constructs_independent_native_root_data_retaining_numerator
      H I E hH e hd hind hGauss hvertex cN hN hn hL r hr hcone
  exact ⟨S, M, cN, rNative, hMlast, hSlast, hrNative, hpower, hmNative, hformula, hnumerator, hpair⟩

end DimensionFourDependence
