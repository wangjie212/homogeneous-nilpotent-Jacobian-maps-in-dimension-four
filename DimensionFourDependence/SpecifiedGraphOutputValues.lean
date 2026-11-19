import DimensionFourDependence.SpecifiedTensorFirstInvariant
import DimensionFourDependence.ActualDevelopableGraphEquations
import DimensionFourDependence.GraphRulingCovectorProjection

/-! # The same tensor realization retains original graph output and root equations -/

namespace DimensionFourDependence

open MvPolynomial Matrix
open scoped TensorProduct

attribute [local instance] Algebra.TensorProduct.rightAlgebra coefficientFieldScalarTower

universe u

set_option quotPrecheck false
set_option maxHeartbeats 1500000
set_option synthInstance.maxHeartbeats 100000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

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
    {d : ℕ} (hd : 0 < d) (hH : IsHomogMap H d)
    (e : RatFunc K ≃ₐ[K] closedGaussParameterField H I)
    {B Z : Type u} [Field B] [Field Z] [Algebra B Z]

local notation "C₀" => closedGaussParameterField H I
local notation "S₀" => FractionRing (MvPolynomial (Fin 4) K)
local notation "T₀" => S₀ ⊗[C₀] E
local notation "F₀" => FractionRing T₀
local notation "xₐ" => extendedClosedGaussAffineTensorCoordinate H I E
local notation "ι" => extendedClosedGaussSourceCoefficientHom H I E
local notation "O" => extendedClosedGaussOutputLinearPolynomial H I E
local notation "Y" => (fun i : Fin 3 => algebraMap (MvPolynomial (Fin 4) K) S₀ (H (p i.castSucc)))
local notation "L" => coefficientField (K := K) (Y)
local notation "a" => actualClosedGaussCoefficientHom H I p hY h hh
local notation "A" => closedGaussCoefficientGraphSlope H I p hY h hh e
local notation "Aₑ" => (fun i => algebraMap C₀ E (e ((A) i)))
local notation "y₀" => coefficientCoordinate (K := K) (Y)

local instance specifiedGraphOutputDomain : IsDomain T₀ :=
  (actual_closed_gauss_cover_algebraic_base_change_isField H I E).isDomain

include hd hH

/-- Euler's original output equation is retained by any compatible
specified graph and finite coefficient embeddings. -/
theorem specified_graph_coefficient_embedding_retains_original_euler_equation
    (g : (L) →+* B) (σ : E →+* B)
    (hσ : ∀ c : C₀, g ((a) c) = σ (algebraMap C₀ E c)) :
    g h = ∑ i : Fin 3, σ ((Aₑ) i) * g ((y₀) i) := by
  have hpartial (i : Fin 3) : g (coefficientPartial (Y) hY i h) = σ ((Aₑ) i) := by
    rw [← closedGaussCoefficientGraphSlope_value H I p hY h hh e i]
    exact hσ (e ((A) i))
  have he := congrArg g (homogeneous_last_output_euler H hd hH p hY h hh)
  rw [coefficientEuler_apply] at he
  simp only [map_sum, map_mul, hpartial] at he
  exact he.symm.trans (Finset.sum_congr rfl (fun i _ => mul_comm _ _))

/-- Every original finite output covector has precisely the value of
its graph restriction on the same original coefficient coordinates. -/
theorem specified_tensor_output_value_eq_original_graph_pairing
    (f : S₀ →+* Z) (g : (L) →+* B) (σ : E →+* B) (φ : F₀ →+* Z)
    (hg : ∀ l : L, algebraMap B Z (g l) = f (l : S₀))
    (hσ : ∀ c : C₀, g ((a) c) = σ (algebraMap C₀ E c))
    (hsource : ∀ s : S₀, φ (algebraMap T₀ F₀ (s ⊗ₜ[C₀] (1 : E))) = f s)
    (hcoeff : ∀ b : E, φ (algebraMap E F₀ b) = algebraMap B Z (σ b))
    (c : Fin 4 → E) :
    φ (aeval (xₐ) ((O) c)) = algebraMap B Z
      ((σ ∘ graphRestrictedCovector p (Aₑ) c) ⬝ᵥ (fun i => g ((y₀) i))) := by
  have he : aeval (xₐ) ((O) c) = ∑ i : Fin 4,
      algebraMap E F₀ (c i) * aeval (xₐ) (MvPolynomial.map (ι) (H i)) := by
    simp only [extendedClosedGaussOutputLinearPolynomial, map_sum, Algebra.smul_def,
      map_mul, AlgHom.commutes]
  have hpoly (i : Fin 4) : φ (aeval (xₐ) (MvPolynomial.map (ι) (H i))) =
      f (algebraMap (MvPolynomial (Fin 4) K) S₀ (H i)) :=
    specified_tensor_realization_original_polynomial_value H I E f φ hsource (H i)
  have heval : φ (aeval (xₐ) ((O) c)) = ∑ i : Fin 4,
      algebraMap B Z (σ (c i)) * f (algebraMap (MvPolynomial (Fin 4) K) S₀ (H i)) := by
    rw [he]
    simp only [map_sum, map_mul, hcoeff, hpoly]
  have hy (i : Fin 3) : f (algebraMap (MvPolynomial (Fin 4) K) S₀ (H (p i.castSucc))) =
      algebraMap B Z (g ((y₀) i)) := (hg ((y₀) i)).symm
  have hlast : f (algebraMap (MvPolynomial (Fin 4) K) S₀ (H (p 3))) =
      algebraMap B Z (g h) := by rw [← hh]; exact (hg h).symm
  calc
    _ = (∑ i : Fin 3, algebraMap B Z (σ (c (p i.castSucc))) *
        algebraMap B Z (g ((y₀) i))) + algebraMap B Z (σ (c (p 3))) *
          algebraMap B Z (g h) := by
      rw [heval, ← Equiv.sum_comp p
        (fun i => algebraMap B Z (σ (c i)) *
          f (algebraMap (MvPolynomial (Fin 4) K) S₀ (H i))), Fin.sum_univ_castSucc]
      simp only [show (Fin.last 3 : Fin 4) = 3 from rfl, hy, hlast]
    _ = algebraMap B Z ((∑ i : Fin 3, σ (c (p i.castSucc)) * g ((y₀) i)) +
        σ (c (p 3)) * g h) := by simp only [map_add, map_sum, map_mul]
    _ = _ := by
      apply congrArg (algebraMap B Z)
      rw [specified_graph_coefficient_embedding_retains_original_euler_equation
        H I p hY h hh E hd hH e g σ hσ]
      simp only [dotProduct, Function.comp_apply, graphRestrictedCovector,
        map_add, map_mul, add_mul, Finset.sum_add_distrib, Finset.mul_sum, mul_assoc]

/-- An original tensor root equation becomes the exact power
equation for that same root and that same graph output covector. -/
theorem specified_tensor_root_power_eq_original_graph_pairing
    (f : S₀ →+* Z) (g : (L) →+* B) (σ : E →+* B) (φ : F₀ →+* Z)
    (hg : ∀ l : L, algebraMap B Z (g l) = f (l : S₀))
    (hσ : ∀ c : C₀, g ((a) c) = σ (algebraMap C₀ E c))
    (hsource : ∀ s : S₀, φ (algebraMap T₀ F₀ (s ⊗ₜ[C₀] (1 : E))) = f s)
    (hcoeff : ∀ b : E, φ (algebraMap E F₀ b) = algebraMap B Z (σ b))
    (c : Fin 4 → E) (r : F₀) (hpower : r ^ d = aeval (xₐ) ((O) c))
    (rho : B) (hrho : φ r = algebraMap B Z rho) :
    rho ^ d = (σ ∘ graphRestrictedCovector p (Aₑ) c) ⬝ᵥ (fun i => g ((y₀) i)) := by
  apply (algebraMap B Z).injective
  calc
    _ = φ (r ^ d) := by simp only [map_pow, hrho]
    _ = _ := by
      rw [hpower]
      exact specified_tensor_output_value_eq_original_graph_pairing H I p hY h hh E hd hH e
        f g σ φ hg hσ hsource hcoeff c

end DimensionFourDependence
