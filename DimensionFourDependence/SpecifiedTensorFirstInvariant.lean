import DimensionFourDependence.NativeGraphNormalComparison
import DimensionFourDependence.SameComponentGraphCoefficients
import DimensionFourDependence.OriginalAffineTensorRealization
import DimensionFourDependence.SourceTensorPolynomialValues

/-! # The specified tensor realization retains the exact original first invariant -/

namespace DimensionFourDependence

open MvPolynomial Matrix
open scoped TensorProduct

attribute [local instance] Algebra.TensorProduct.rightAlgebra coefficientFieldScalarTower

universe u

set_option quotPrecheck false
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 10000
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

variable {K : Type u} [Field K] [CharZero K]
    (H : Fin 4 → MvPolynomial (Fin 4) K) (I : ImageRelationWitness H)
    (p : Equiv.Perm (Fin 4))
    (hY : AlgebraicIndependent K (fun i : Fin 3 => algebraMap (MvPolynomial (Fin 4) K)
      (FractionRing (MvPolynomial (Fin 4) K)) (H (p i.castSucc))))
    (h : coefficientField (K := K) (fun i : Fin 3 => algebraMap (MvPolynomial (Fin 4) K)
      (FractionRing (MvPolynomial (Fin 4) K)) (H (p i.castSucc))))
    (hh : (h : FractionRing (MvPolynomial (Fin 4) K)) = algebraMap (MvPolynomial (Fin 4) K)
      (FractionRing (MvPolynomial (Fin 4) K)) (H (p 3)))
    (E : Type u) [Field E] [Algebra (closedGaussParameterField H I) E]
    [Algebra.IsAlgebraic (closedGaussParameterField H I) E]
    {B Z : Type u} [Field B] [Field Z] [Algebra B Z]

local notation "C₀" => closedGaussParameterField H I
local notation "S₀" => FractionRing (MvPolynomial (Fin 4) K)
local notation "T₀" => S₀ ⊗[C₀] E
local notation "F₀" => FractionRing T₀
local notation "xₐ" => extendedClosedGaussAffineTensorCoordinate H I E
local notation "Y" => (fun i : Fin 3 => algebraMap (MvPolynomial (Fin 4) K) S₀ (H (p i.castSucc)))
local notation "L" => coefficientField (K := K) (Y)
local notation "a" => actualClosedGaussCoefficientHom H I p hY h hh
local notation "ν" => actualClosedGaussFirstInvariantCovector H I p hY h hh

local instance specifiedTensorFirstInvariantDomain : IsDomain T₀ :=
  (actual_closed_gauss_cover_algebraic_base_change_isField H I E).isDomain

/-- Agreement of the graph and finite coefficient maps on the
entire original closed Gauss field gives its exact source value under
the same source embedding. -/
theorem compatible_graph_and_finite_coefficients_retain_closed_source_values
    (f : S₀ →+* Z) (g : (L) →+* B) (σ : E →+* B)
    (hg : ∀ l : L, algebraMap B Z (g l) = f (l : S₀))
    (hσ : ∀ c : C₀, g ((a) c) = σ (algebraMap C₀ E c)) (c : C₀) :
    f (c : S₀) = algebraMap B Z (σ (algebraMap C₀ E c)) := by
  calc
    _ = f (algebraMap (L) S₀ ((a) c)) :=
      congrArg f (original_closed_gauss_graph_inclusion_source_value H I p hY h hh c).symm
    _ = algebraMap B Z (g ((a) c)) := (hg ((a) c)).symm
    _ = _ := congrArg (algebraMap B Z) (hσ c)

omit p hY h hh in
/-- Original polynomial values pass through the same specified
tensor realization and original source map. -/
theorem specified_tensor_realization_original_polynomial_value
    (f : S₀ →+* Z) (φ : F₀ →+* Z)
    (hsource : ∀ s : S₀, φ (algebraMap T₀ F₀ (s ⊗ₜ[C₀] (1 : E))) = f s)
    (P : MvPolynomial (Fin 4) K) :
    φ (aeval (xₐ) (MvPolynomial.map (extendedClosedGaussSourceCoefficientHom H I E) P)) =
      f (algebraMap (MvPolynomial (Fin 4) K) S₀ P) := by
  have he := comp_aeval_apply (extendedClosedGaussSourceTensorCoordinate H I E)
    (IsScalarTower.toAlgHom E T₀ F₀)
    (MvPolynomial.map (extendedClosedGaussSourceCoefficientHom H I E) P)
  change algebraMap T₀ F₀ (aeval (extendedClosedGaussSourceTensorCoordinate H I E)
    (MvPolynomial.map (extendedClosedGaussSourceCoefficientHom H I E) P)) =
      aeval (xₐ) (MvPolynomial.map (extendedClosedGaussSourceCoefficientHom H I E) P) at he
  rw [← he, extendedClosedGaussSourceTensorCoordinate_original_constant_polynomial_value, hsource]

omit p hY h hh in
/-- A specified realization of the original affine tensor fraction
field is injective. Keeping this field argument separate avoids
reconstructing its field structure in a later coefficient tower. -/
theorem specified_original_affine_tensor_realization_injective
    (φ : F₀ →+* Z) : Function.Injective φ :=
  @RingHom.injective F₀ Z _
    (@DivisionRing.isSimpleRing F₀ (@Field.toDivisionRing F₀ (inferInstance : Field F₀)))
    _ _ φ

variable {d : ℕ} (hH : IsHomogMap H d) (hd : 0 < d)
    (hind : ¬ComponentsDependent H) (hGauss : gaussImageDimension H I = 1)
    (e : RatFunc K ≃ₐ[K] closedGaussParameterField H I)

local notation "A₀" => extendedClosedGaussChosenRulingMatrix H I E hH hd hind hGauss
local notation "L₀" => linearFormPolynomial ((A₀) 0)
local notation "a₀" => actualClosedGaussNormalCovector H I e (p 3)

/-- The chosen normal form has exactly the original first invariant
times the specified nonzero normal pivot in this same realization. -/
theorem specified_tensor_normal_value_eq_original_first_invariant
    (f : S₀ →+* Z) (g : (L) →+* B) (σ : E →+* B) (φ : F₀ →+* Z)
    (hg : ∀ l : L, algebraMap B Z (g l) = f (l : S₀))
    (hσ : ∀ c : C₀, g ((a) c) = σ (algebraMap C₀ E c))
    (hcoeff : ∀ b : E, φ (algebraMap E F₀ b) = algebraMap B Z (σ b))
    (hcoords : ∀ i, φ ((xₐ) i) = f (rationalCoordinate (K := K) i))
    (c : L) (hc : (c : S₀) = firstFiberInvariantInChart p (Y) hY h) :
    φ (aeval (xₐ) (L₀)) = algebraMap B Z (σ (algebraMap C₀ E (a₀)) * g c) := by
  have hfC (b : C₀) : f (algebraMap C₀ S₀ b) = algebraMap B Z (σ (algebraMap C₀ E b)) :=
    compatible_graph_and_finite_coefficients_retain_closed_source_values H I p hY h hh E f g σ hg hσ b
  have hνvalue := actualClosedGaussFirstInvariantCovector_source_value H I p hY h hh
  simp only [linearFormPolynomial, map_sum, map_mul, aeval_C, aeval_X] at hνvalue
  have hνsum : (∑ i : Fin 4, algebraMap B Z (σ (algebraMap C₀ E ((ν) i))) *
      f (rationalCoordinate (K := K) i)) = algebraMap B Z (g c) := by
    have he := congrArg f (hνvalue.trans hc.symm)
    simpa only [map_sum, map_mul, hfC] using he.trans (hg c).symm
  have hrow (i : Fin 4) : σ ((A₀) 0 i) =
      σ (algebraMap C₀ E (a₀)) * σ (algebraMap C₀ E ((ν) i)) := by
    rw [extendedClosedGaussChosenRulingMatrix_first_row_eq_graph_pivot_mul H I p hY h hh E e hH hd hind hGauss,
      map_mul]
  have hLformula : aeval (xₐ) (L₀) =
      ∑ i : Fin 4, algebraMap E F₀ ((A₀) 0 i) * (xₐ) i := by
    simp only [linearFormPolynomial, map_sum, map_mul, aeval_C, aeval_X]
  calc
    _ = ∑ i : Fin 4, φ (algebraMap E F₀ ((A₀) 0 i) * (xₐ) i) :=
      (congrArg φ hLformula).trans (map_sum φ.toAddMonoidHom _ _)
    _ = algebraMap B Z (σ (algebraMap C₀ E (a₀))) *
        (∑ i : Fin 4, algebraMap B Z (σ (algebraMap C₀ E ((ν) i))) *
          f (rationalCoordinate (K := K) i)) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      rw [map_mul, hcoeff, hcoords, hrow, map_mul]
      ring
    _ = _ := by rw [hνsum, map_mul]

/-- The root scalar is determined by the original first invariant,
with the original plane scale and original normal pivot. -/
theorem specified_scaled_plane_root_scalar_eq_original_first_invariant
    (f : S₀ →+* Z) (g : (L) →+* B) (σ : E →+* B) (φ : F₀ →+* Z)
    (hg : ∀ l : L, algebraMap B Z (g l) = f (l : S₀))
    (hσ : ∀ c : C₀, g ((a) c) = σ (algebraMap C₀ E c))
    (hcoeff : ∀ b : E, φ (algebraMap E F₀ b) = algebraMap B Z (σ b))
    (hcoords : ∀ i, φ ((xₐ) i) = f (rationalCoordinate (K := K) i))
    (c : L) (hc : (c : S₀) = firstFiberInvariantInChart p (Y) hY h)
    (r : F₀) (u : E) (hscaled : r = algebraMap E F₀ u * aeval (xₐ) (L₀))
    (rho : B) (hrho : φ r = algebraMap B Z rho) :
    rho = σ u * σ (algebraMap C₀ E (a₀)) * g c := by
  apply (algebraMap B Z).injective
  calc
    _ = φ r := hrho.symm
    _ = algebraMap B Z (σ u) * algebraMap B Z (σ (algebraMap C₀ E (a₀)) * g c) := by
      rw [hscaled, map_mul, hcoeff,
        specified_tensor_normal_value_eq_original_first_invariant H I p hY h hh E hH hd hind hGauss e
          f g σ φ hg hσ hcoeff hcoords c hc]
    _ = _ := by simp only [map_mul, mul_assoc]

end DimensionFourDependence
