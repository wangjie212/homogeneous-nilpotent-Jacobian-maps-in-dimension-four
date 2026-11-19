import DimensionFourDependence.ComponentOriginalOutputValues
import DimensionFourDependence.SpecifiedAffineRootEquations

/-! # The same full generic component retains the original finite root equations -/

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
local notation "D₀" => polynomialOutputField H
local notation "ι" => extendedClosedGaussSourceCoefficientHom H I E
local notation "A₀" => extendedClosedGaussChosenRulingMatrix H I E hH hd hind hGauss
local notation "H₀" => (fun i => algebraMap (MvPolynomial (Fin 4) K) S₀ (H i))

local instance geometricComponentSpecifiedRootsDomain : IsDomain T₀ :=
  (actual_closed_gauss_cover_algebraic_base_change_isField H I E).isDomain

variable {B Z : Type u} [Field B] [Field Z] [IsAlgClosed B] [Algebra B Z]

/-- The original three finite covectors, nonzero root and exact
equations in one specified source/coefficient realization. -/
noncomputable def OriginalFiniteRootEquationsOnRealization
    (φ : F₀ →+* Z) (σ : E →+* B) (x : Fin 4 → Z) (y : Fin 4 → B) : Prop :=
  ∃ (cS cM cN : Fin 4 → E) (R : B),
    cS ≠ 0 ∧ cM ≠ 0 ∧ cN ≠ 0 ∧ cN (Fin.last 3) = 0 ∧
    (∑ i, σ (cM i) * y i) ≠ 0 ∧ (∑ i, σ (cN i) * y i) ≠ 0 ∧
    R ≠ 0 ∧ R ^ d = ∑ i, σ (cS i) * y i ∧
    let Λ := ∑ i, algebraMap B Z (σ ((A₀) 0 i)) * x i
    algebraMap B Z R = algebraMap B Z (∑ i, σ (cN i) * y i) * Λ /
      algebraMap B Z (∑ i, σ (cM i) * y i) ∧
    ((∃ γ : E, γ ≠ 0 ∧ algebraMap B Z R = algebraMap B Z (σ γ⁻¹) * Λ) ∨
      ∃ r : F₀, φ r = algebraMap B Z R ∧
        AffineSourceFixedVertexConeRootForm H I E hH hd hind hGauss r)

/-- On the same actual full generic component, a compatible tensor
realization retains all three original finite covectors and derives
their exact root equations over the actual generic output constants.
The output equations are consequences of component minimality, rather
than separate assumptions. -/
theorem full_generic_component_tensor_embedding_retains_original_finite_root_equations
    (δ : D₀ →+* B) (σ : E →+* B)
    (hσK : ∀ c : K, σ ((ι) c) = δ (algebraMap K D₀ c))
    (x : Fin 4 → Z) (φ : F₀ →+* Z)
    (hcoeff : ∀ b : E, φ (algebraMap E F₀ b) = algebraMap B Z (σ b))
    (hcoords : ∀ i, φ ((xₐ) i) = x i)
    (hdata : ActualAffineFixedVertexRootAlternatives H I E hH hd hind hGauss) :
    letI : Algebra D₀ B := δ.toAlgebra
    fiberVanishingIdeal (L := B) x ∈
      (extendCoefficientIdeal B (fiberVanishingIdeal (L := D₀)
        (rationalCoordinate (K := K) (n := 4)))).minimalPrimes →
    let y : Fin 4 → B := fun i => δ (fullOutputCoordinate (K := K) (H₀) i)
    OriginalFiniteRootEquationsOnRealization H I E hH hd hind hGauss φ σ x y := by
  letI : Algebra D₀ B := δ.toAlgebra
  intro hcomponent
  let y : Fin 4 → B := fun i => δ (fullOutputCoordinate (K := K) (H₀) i)
  have hpoly (P : MvPolynomial (Fin 4) E) : φ (aeval (xₐ) P) =
      MvPolynomial.eval₂ ((algebraMap B Z).comp σ) x P := by
    rw [MvPolynomial.map_aeval]
    have hc : φ.comp (algebraMap E F₀) = (algebraMap B Z).comp σ := RingHom.ext hcoeff
    rw [hc, show (fun i => φ ((xₐ) i)) = x from funext hcoords]
    rfl
  have hk : ((algebraMap B Z).comp σ).comp (ι) =
      ((algebraMap B Z).comp δ).comp (algebraMap K D₀) := by
    apply RingHom.ext
    intro c
    exact congrArg (algebraMap B Z) (hσK c)
  have hout (i : Fin 4) : φ (aeval (xₐ) (MvPolynomial.map (ι) (H i))) =
      algebraMap B Z (y i) := by
    rw [hpoly, MvPolynomial.eval₂_map, hk]
    exact full_generic_component_original_output_values H δ x hcomponent i
  simpa only [OriginalFiniteRootEquationsOnRealization, hcoords] using
    actual_affine_root_equations_retained_by_specified_tensor_embedding
      H I E hH hd hind hGauss φ σ hcoeff y hout hdata

end DimensionFourDependence
