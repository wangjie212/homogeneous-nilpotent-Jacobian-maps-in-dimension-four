import DimensionFourDependence.AffinePencilBaseRelations
import DimensionFourDependence.AffineFixedVertexRootAlternatives
import DimensionFourDependence.FixedVertexNumeratorBaseZero

/-! # The actual scaled-plane root gives a power relation on the pencil base

The constructed affine root alternatives retain the original numerator
which annihilates the vertex. In the scaled-plane branch their exact
power identity supplies a polynomial congruence on the whole original
coefficient-extended base, with no assumed restriction identity at that
base and no denominator-nonvanishing condition there.
-/

namespace DimensionFourDependence

open MvPolynomial
open scoped TensorProduct

attribute [local instance] Algebra.TensorProduct.rightAlgebra

universe u

set_option quotPrecheck false
set_option maxHeartbeats 3000000
set_option synthInstance.maxHeartbeats 100000
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

variable {K : Type u} [Field K] [CharZero K]
    (H : Fin 4 → MvPolynomial (Fin 4) K) (I : ImageRelationWitness H)
    (E : Type u) [Field E] [Algebra (closedGaussParameterField H I) E]
    [Algebra.IsAlgebraic (closedGaussParameterField H I) E]
    {d : ℕ} (hH : IsHomogMap H d) (hd : 0 < d)
    (hind : ¬ComponentsDependent H) (hGauss : gaussImageDimension H I = 1)
    (e : RatFunc K ≃ₐ[K] closedGaussParameterField H I)

local notation "C₀" => closedGaussParameterField H I
local notation "S₀" => FractionRing (MvPolynomial (Fin 4) K)
local notation "T₀" => S₀ ⊗[C₀] E
local notation "F₀" => FractionRing T₀
local notation "xₐ" => extendedClosedGaussAffineTensorCoordinate H I E
local notation "O" => extendedClosedGaussOutputLinearPolynomial H I E
local notation "L₀" => linearFormPolynomial
  (extendedClosedGaussChosenRulingMatrix H I E hH hd hind hGauss 0)
local notation "ι" => extendedClosedGaussSourceCoefficientHom H I E

local instance scaledPlaneBasePowerDomain : IsDomain T₀ :=
  (actual_closed_gauss_cover_algebraic_base_change_isField H I E).isDomain

/-- The actual affine alternatives either retain their complete cone
form or construct the scaled-plane power congruence on the original
pencil base. The nonzero original numerator and its vertex vanishing
are retained in both cases. -/
theorem actual_affine_root_alternatives_construct_base_power_relation
    (hvertex : rationalImageNormal H I.equation (Fin.last 3) = 0)
    (p q : MvPolynomial (Fin 4) K) (hq : q ≠ 0) (hrel : IsRelPrime p q)
    (hparameter : closedGaussParameterSourceHom H I e RatFunc.X =
      algebraMap (MvPolynomial (Fin 4) K) S₀ p / algebraMap (MvPolynomial (Fin 4) K) S₀ q)
    (hdata : ActualAffineFixedVertexRootAlternatives H I E hH hd hind hGauss) :
    ∃ (cS cN : Fin 4 → E) (r : F₀), cS ≠ 0 ∧ cN ≠ 0 ∧ cN (Fin.last 3) = 0 ∧
      aeval (xₐ) ((O) cN) ≠ 0 ∧
      (O) cN ∈ (Ideal.span ({MvPolynomial.map (ι) p, MvPolynomial.map (ι) q} :
        Set (MvPolynomial (Fin 4) E))).radical ∧ r ≠ 0 ∧ r ^ d = aeval (xₐ) ((O) cS) ∧
      ((∃ a : E, a ≠ 0 ∧ r = algebraMap E F₀ a * aeval (xₐ) (L₀) ∧
        (O) cS - C (a ^ d) * (L₀) ^ d ∈
          Ideal.span ({MvPolynomial.map (ι) p, MvPolynomial.map (ι) q} :
            Set (MvPolynomial (Fin 4) E))) ∨
        AffineSourceFixedVertexConeRootForm H I E hH hd hind hGauss r) := by
  obtain ⟨cS, cM, cN, hS, hM, hN, hnlast, hm, hr, hpower, halt⟩ := hdata
  let r : F₀ := aeval (xₐ) ((O) cN) * aeval (xₐ) (L₀) / aeval (xₐ) ((O) cM)
  have hnvalue : aeval (xₐ) ((O) cN) ≠ 0 := by
    intro hz
    apply hr
    rw [hz, zero_mul, zero_div]
  have hnbase := vertex_output_covector_mem_extended_pencil_base_radical
    H I E hd hH hind hGauss hvertex e p q hq hrel hparameter cN hnlast
  refine ⟨cS, cN, r, hS, hN, hnlast, hnvalue, hnbase, hr, hpower, ?_⟩
  rcases halt with ⟨a, ha, hplane⟩ | hcone
  · left
    refine ⟨a⁻¹, inv_ne_zero ha, hplane, ?_⟩
    apply affine_tensor_relation_mem_pencil_base_ideal H I E e p q hq hrel hparameter
    simp only [map_sub, map_mul, aeval_C, map_pow]
    apply sub_eq_zero.mpr
    calc
      aeval (xₐ) ((O) cS) = r ^ d := hpower.symm
      _ = (algebraMap E F₀ a⁻¹ * aeval (xₐ) (L₀)) ^ d := congrArg (fun z : F₀ => z ^ d) hplane
      _ = (algebraMap E F₀ a⁻¹) ^ d * (aeval (xₐ) (L₀)) ^ d := by rw [mul_pow]
  · exact Or.inr hcone

end DimensionFourDependence
