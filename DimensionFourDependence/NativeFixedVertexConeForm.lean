import DimensionFourDependence.FixedVertexCharacteristicAxis
import DimensionFourDependence.NativeProportionalPowerFactorization

/-! # The characteristic root factorization constructs the full cone formula

The specified fixed vertex is the actual characteristic axis. Its nonzero
coefficient therefore gives the nonzero fourth-coordinate coefficient in
(4.7), while all transverse characteristic coefficients vanish. The
original ruling equations give both ternary normal incidences.
-/

namespace DimensionFourDependence

open MvPolynomial Matrix Module AlgebraicGeometry

universe u

set_option quotPrecheck false
set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 100000

variable {K : Type u} [Field K] [CharZero K]
    (H : Fin 4 → MvPolynomial (Fin 4) K) (I : ImageRelationWitness H)
    (E : Type u) [Field E] [Algebra (closedGaussParameterField H I) E]
    [Algebra.IsAlgebraic (closedGaussParameterField H I) E]
    {d : ℕ} (hH : IsHomogMap H d) (e : RatFunc K ≃ₐ[K] closedGaussParameterField H I)
    (hd : 0 < d) (hind : ¬ ComponentsDependent H) (hGauss : gaussImageDimension H I = 1)

local notation "N" => extendedClosedGaussNormalizationScheme H I E hH e
local notation "w" => extendedClosedGaussNormalizationHyperplaneWeight H I E hH e
local notation "A₀" => extendedClosedGaussChosenRulingMatrix H I E hH hd hind hGauss
local notation "Y₀" => fun i => aeval (w) (MvPolynomial.map (extendedClosedGaussSourceCoefficientHom H I E) (H i))

local instance nativeFixedVertexConeFormIntegral : IsIntegral N :=
  extendedClosedGaussNormalizationScheme_isIntegral H I E hH e
noncomputable local instance nativeFixedVertexConeFormAlgebra : Algebra E (N).functionField :=
  extendedClosedGaussOwnFunctionFieldAlgebra H I E hH e

/-- The entire actual native cone formula (4.7), with a nonzero
fourth coefficient and both original ternary ruling equations. -/
noncomputable def NativeFixedVertexConeRootForm (r : (N).functionField) : Prop :=
  ∃ (V : Fin 3 → E) (a b : E), V ≠ 0 ∧ b ≠ 0 ∧
    (∀ q : Fin 2, (∑ i : Fin 3, (A₀) q i.castSucc * V i) = 0) ∧
    (∀ i : Fin 3, (Y₀) i.castSucc = algebraMap E (N).functionField (V i) * r ^ d) ∧
    (Y₀) (Fin.last 3) = algebraMap E (N).functionField a * r ^ d +
      algebraMap E (N).functionField b * r ^ (d - 1) *
        (∑ i : Fin 3, algebraMap E (N).functionField ((A₀) 0 i.castSucc) * (w) i.castSucc)

/-- The actual characteristic root factorization constructs every
coordinate of (4.7). Its last coefficient is nonzero because its
characteristic factor is a nonzero vector on the proved fourth axis. -/
theorem native_characteristic_root_constructs_full_fixed_vertex_cone_form
    (hvertex : rationalImageNormal H I.equation (Fin.last 3) = 0)
    (cN : Fin 4 → E) (r : (N).functionField)
    (hfactor : CharacteristicNativeRulingRootFactorization H I E hH e hd hind hGauss cN r) :
    NativeFixedVertexConeRootForm H I E hH e hd hind hGauss r := by
  classical
  obtain ⟨V, W, hLI, hV, _hW, hchar, _hspan, _hzero, hvalues⟩ := hfactor
  have hW0 : W ≠ 0 := by simpa using hLI.ne_zero (1 : Fin 2)
  obtain ⟨hWfirst, hWlast, _hWaxis⟩ := extended_chosen_characteristic_fixed_vertex_coordinates
    H I E hH hd hind hGauss hvertex W hW0 hchar
  have hcol := extended_chosen_ruling_fixed_vertex_last_column H I E hH hd hind hGauss hvertex
  have hVfirst : (fun i : Fin 3 => V i.castSucc) ≠ 0 := by
    intro hz
    have hprop : (V (Fin.last 3) / W (Fin.last 3)) • W = V := by
      funext i
      refine Fin.lastCases ?_ (fun i => ?_) i
      · change V (Fin.last 3) / W (Fin.last 3) * W (Fin.last 3) = V (Fin.last 3)
        exact div_mul_cancel₀ _ hWlast
      · change V (Fin.last 3) / W (Fin.last 3) * W i.castSucc = V i.castSucc
        rw [hWfirst, mul_zero]
        exact (congrFun hz i).symm
    exact (LinearIndependent.pair_iff' hW0).mp (LinearIndependent.pair_symm_iff.mp hLI) _ hprop
  have hL : (∑ i : Fin 4, algebraMap E (N).functionField ((A₀) 0 i) * (w) i) =
      ∑ i : Fin 3, algebraMap E (N).functionField ((A₀) 0 i.castSucc) * (w) i.castSucc := by
    rw [Fin.sum_univ_castSucc, hcol, map_zero, zero_mul, add_zero]
  refine ⟨fun i => V i.castSucc, V (Fin.last 3), W (Fin.last 3), hVfirst, hWlast, ?_, ?_, ?_⟩
  · intro q
    change (A₀) *ᵥ V = 0 at hV
    have he := congrFun hV q
    simpa only [mulVec, dotProduct, Fin.sum_univ_castSucc, hcol, zero_mul, add_zero, Pi.zero_apply] using he
  · intro i
    rw [hvalues, hWfirst, map_zero, mul_zero, add_zero]
    have hp : r ^ (d - 1) * r = r ^ d := by rw [← pow_succ]; congr 1; omega
    rw [← mul_assoc, hp, mul_comm]
  · rw [hvalues, hL]
    have hp : r ^ (d - 1) * r = r ^ d := by rw [← pow_succ]; congr 1; omega
    rw [mul_add, ← mul_assoc, hp]
    ring

end DimensionFourDependence
