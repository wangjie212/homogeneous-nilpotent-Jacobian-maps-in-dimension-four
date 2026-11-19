import DimensionFourDependence.AffineFixedVertexRootAlternatives
import DimensionFourDependence.ParabolaFieldEmbedding

/-! # Original finite root covectors and equations under a specified tensor embedding -/

namespace DimensionFourDependence

open MvPolynomial
open scoped TensorProduct

attribute [local instance] Algebra.TensorProduct.rightAlgebra

universe u

set_option quotPrecheck false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 100000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {K : Type u} [Field K] [CharZero K]
    (H : Fin 4 → MvPolynomial (Fin 4) K) (I : ImageRelationWitness H)
    (E : Type u) [Field E] [Algebra (closedGaussParameterField H I) E]
    [Algebra.IsAlgebraic (closedGaussParameterField H I) E]
    {d : ℕ} (hH : IsHomogMap H d) (hd : 0 < d)
    (hind : ¬ComponentsDependent H) (hGauss : gaussImageDimension H I = 1)

local notation "C₀" => closedGaussParameterField H I
local notation "S₀" => FractionRing (MvPolynomial (Fin 4) K)
local notation "T₀" => S₀ ⊗[C₀] E
local notation "F₀" => FractionRing T₀
local notation "xₐ" => extendedClosedGaussAffineTensorCoordinate H I E
local notation "ι" => extendedClosedGaussSourceCoefficientHom H I E
local notation "O" => extendedClosedGaussOutputLinearPolynomial H I E
local notation "A₀" => extendedClosedGaussChosenRulingMatrix H I E hH hd hind hGauss
local notation "L₀" => linearFormPolynomial ((A₀) 0)

local instance specifiedAffineRootEquationsDomain : IsDomain T₀ :=
  (actual_closed_gauss_cover_algebraic_base_change_isField H I E).isDomain

variable {B Z : Type u} [Field B] [Field Z] [IsAlgClosed B] [Algebra B Z]

/-- The specified coefficient embedding retains all three original
finite covectors, the nonzero numerator and denominator, and the exact
rational root equation. The root is an actual nonzero geometric
constant. Neither coefficients nor root covectors are replaced by a
newly chosen conjugate realization. Both original alternatives remain. -/
theorem actual_affine_root_equations_retained_by_specified_tensor_embedding
    (φ : F₀ →+* Z) (σ : E →+* B)
    (hcoeff : ∀ b : E, φ (algebraMap E F₀ b) = algebraMap B Z (σ b))
    (y : Fin 4 → B)
    (hout : ∀ i, φ (aeval (xₐ) (MvPolynomial.map (ι) (H i))) = algebraMap B Z (y i))
    (hdata : ActualAffineFixedVertexRootAlternatives H I E hH hd hind hGauss) :
    ∃ (cS cM cN : Fin 4 → E) (R : B),
      cS ≠ 0 ∧ cM ≠ 0 ∧ cN ≠ 0 ∧ cN (Fin.last 3) = 0 ∧
      (∑ i, σ (cM i) * y i) ≠ 0 ∧ (∑ i, σ (cN i) * y i) ≠ 0 ∧
      R ≠ 0 ∧ R ^ d = ∑ i, σ (cS i) * y i ∧
      let Λ := ∑ i, algebraMap B Z (σ ((A₀) 0 i)) * φ ((xₐ) i)
      algebraMap B Z R = algebraMap B Z (∑ i, σ (cN i) * y i) * Λ /
        algebraMap B Z (∑ i, σ (cM i) * y i) ∧
      ((∃ γ : E, γ ≠ 0 ∧ algebraMap B Z R = algebraMap B Z (σ γ⁻¹) * Λ) ∨
        ∃ r : F₀, φ r = algebraMap B Z R ∧
          AffineSourceFixedVertexConeRootForm H I E hH hd hind hGauss r) := by
  have houtput (c : Fin 4 → E) : φ (aeval (xₐ) ((O) c)) =
      algebraMap B Z (∑ i, σ (c i) * y i) := by
    have he : aeval (xₐ) ((O) c) = ∑ i : Fin 4,
        algebraMap E F₀ (c i) * aeval (xₐ) (MvPolynomial.map (ι) (H i)) := by
      simp only [extendedClosedGaussOutputLinearPolynomial, map_sum, Algebra.smul_def,
        map_mul, AlgHom.commutes]
    rw [he]
    simp only [map_sum, map_mul, hcoeff, hout]
  have hlinear : φ (aeval (xₐ) (L₀)) =
      ∑ i, algebraMap B Z (σ ((A₀) 0 i)) * φ ((xₐ) i) := by
    simp only [linearFormPolynomial, map_sum, map_mul, aeval_C, aeval_X, hcoeff]
  obtain ⟨cS, cM, cN, hS, hM, hN, hnlast, hm, hr, hpower, halt⟩ := hdata
  let r : F₀ := aeval (xₐ) ((O) cN) * aeval (xₐ) (L₀) / aeval (xₐ) ((O) cM)
  have hpow : (φ r) ^ d = algebraMap B Z (∑ i, σ (cS i) * y i) := by
    rw [← map_pow]
    exact (congrArg φ hpower).trans (houtput cS)
  have hralg : IsAlgebraic B (φ r) := IsAlgebraic.of_pow hd
    (by rw [hpow]; exact isAlgebraic_algebraMap _)
  obtain ⟨R, hR⟩ := algebraic_value_preimage_of_isAlgClosed (φ r) hralg
  have hR0 : R ≠ 0 := by
    intro hz
    apply hr
    apply φ.injective
    change φ r = φ 0
    rw [← hR, hz, map_zero, map_zero]
  have hRp : R ^ d = ∑ i, σ (cS i) * y i := by
    apply (algebraMap B Z).injective
    rw [map_pow, hR, hpow]
  have hn : aeval (xₐ) ((O) cN) ≠ 0 := by
    intro hz
    apply hr
    rw [hz, zero_mul, zero_div]
  have hMout : (∑ i, σ (cM i) * y i) ≠ 0 := by
    intro hz
    apply hm
    apply φ.injective
    rw [houtput, hz, map_zero, map_zero]
  have hNout : (∑ i, σ (cN i) * y i) ≠ 0 := by
    intro hz
    apply hn
    apply φ.injective
    rw [houtput, hz, map_zero, map_zero]
  refine ⟨cS, cM, cN, R, hS, hM, hN, hnlast, hMout, hNout, hR0, hRp, ?_, ?_⟩
  · rw [hR]
    change φ (aeval (xₐ) ((O) cN) * aeval (xₐ) (L₀) / aeval (xₐ) ((O) cM)) = _
    rw [map_div₀, map_mul, houtput, houtput, hlinear]
  · rcases halt with ⟨γ, hγ, hplane⟩ | hcone
    · left
      refine ⟨γ, hγ, ?_⟩
      rw [hR]
      exact (congrArg φ hplane).trans (by rw [map_mul, hcoeff, hlinear])
    · exact Or.inr ⟨r, hR.symm, hcone⟩

end DimensionFourDependence
