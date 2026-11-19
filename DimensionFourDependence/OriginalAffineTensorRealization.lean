import DimensionFourDependence.AlgebraicSourceTensorRealization
import DimensionFourDependence.AffineSourceConeForm

/-! # A fixed compatible coefficient realization retains the entire original affine source tensor -/

namespace DimensionFourDependence

open MvPolynomial
open scoped TensorProduct

attribute [local instance] Algebra.TensorProduct.rightAlgebra

universe u

set_option quotPrecheck false
set_option maxHeartbeats 3000000
set_option synthInstance.maxHeartbeats 100000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {K : Type u} [Field K] [CharZero K]
    (H : Fin 4 → MvPolynomial (Fin 4) K) (I : ImageRelationWitness H)
    (E : Type u) [Field E] [Algebra (closedGaussParameterField H I) E]
    [Algebra.IsAlgebraic (closedGaussParameterField H I) E]

local notation "C₀" => closedGaussParameterField H I
local notation "S₀" => FractionRing (MvPolynomial (Fin 4) K)
local notation "T₀" => S₀ ⊗[C₀] E
local notation "F₀" => FractionRing T₀
local notation "xₐ" => extendedClosedGaussAffineTensorCoordinate H I E

local instance originalAffineTensorRealizationDomain : IsDomain T₀ :=
  (actual_closed_gauss_cover_algebraic_base_change_isField H I E).isDomain

/-- A specified source embedding and specified algebraic coefficient
embedding, compatible on the whole original closed Gauss field, give one
actual affine tensor fraction-field realization. It retains every source
value, coefficient, original coordinate and extended polynomial value. -/
theorem compatible_original_closed_coefficients_construct_affine_tensor_realization
    {Z : Type u} [Field Z] (f : S₀ →+* Z) (τ : E →+* Z)
    (hclosed : ∀ c : C₀, f (c : S₀) = τ (algebraMap C₀ E c)) :
    ∃ φ : F₀ →+* Z,
      (∀ s : S₀, φ (algebraMap T₀ F₀ (s ⊗ₜ[C₀] (1 : E))) = f s) ∧
      (∀ b : E, φ (algebraMap E F₀ b) = τ b) ∧
      (∀ i : Fin 4, φ ((xₐ) i) = f (rationalCoordinate (K := K) i)) ∧
      ∀ P : MvPolynomial (Fin 4) E,
        φ (aeval (xₐ) P) = MvPolynomial.eval₂ τ (fun i => f (rationalCoordinate (K := K) i)) P := by
  letI : CharZero C₀ := charZero_of_injective_algebraMap (algebraMap K C₀).injective
  letI : Algebra C₀ Z := (τ.comp (algebraMap C₀ E)).toAlgebra
  let fC : S₀ →ₐ[C₀] Z := { f with commutes' := hclosed }
  let τC : E →ₐ[C₀] Z := { τ with commutes' := fun _ => rfl }
  obtain ⟨φ, hsource, hcoeff⟩ := relatively_closed_algebraic_source_tensor_constructs_fraction_realization
    (closedGaussParameterField_relatively_closed H I) fC τC
  have hcoeffE (b : E) : φ (algebraMap E F₀ b) = τ b := by
    rw [IsScalarTower.algebraMap_apply E T₀ F₀]
    exact hcoeff b
  have hcoords (i : Fin 4) : φ ((xₐ) i) = f (rationalCoordinate (K := K) i) :=
    hsource (rationalCoordinate (K := K) i)
  let ψ : F₀ →+* Z :=
    { toFun := fun x => φ x
      map_zero' := map_zero φ
      map_one' := map_one φ
      map_add' := fun x y => map_add φ x y
      map_mul' := fun x y => map_mul φ x y }
  refine ⟨ψ, hsource, hcoeffE, hcoords, ?_⟩
  intro P
  rw [MvPolynomial.map_aeval]
  have hc : ψ.comp (algebraMap E F₀) = τ := RingHom.ext hcoeffE
  have hx : (fun i => ψ ((xₐ) i)) =
      (fun i => f (rationalCoordinate (K := K) i)) := funext hcoords
  rw [hc, hx]
  rfl

end DimensionFourDependence
