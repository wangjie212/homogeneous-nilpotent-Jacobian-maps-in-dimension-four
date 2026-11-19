import DimensionFourDependence.AlgebraicSourceDerivationChain
import DimensionFourDependence.ParabolicFiberDerivation

/-! # The actual parabolic fiber derivative is the constructed source-frame direction -/

namespace DimensionFourDependence

open MvPolynomial Matrix

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 100000
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

variable {K E F : Type*} [Field K] [CharZero K] [Field E] [Field F]
    [Algebra K E] [Algebra K F] [Algebra E F] [IsScalarTower K E F]
    [Algebra (FractionRing (MvPolynomial (Fin 4) K)) F]
    [IsScalarTower K (FractionRing (MvPolynomial (Fin 4) K)) F]
    [Algebra.IsAlgebraic (FractionRing (MvPolynomial (Fin 4) K)) F]

local notation "S₀" => FractionRing (MvPolynomial (Fin 4) K)
local notation "x₀" => fun i : Fin 4 => algebraMap S₀ F (rationalCoordinate (K := K) i)
local notation "D₀" => algebraicPartial (K := K) F

/-- The actual projected line and vertex parabola construct one
constant-field derivation equal to the original source's transverse
frame direction, with its exact slope and quadratic acceleration. -/
theorem actual_parabolic_source_constructs_transverse_frame_derivation
    (p : RatFunc K →ₐ[K] F) (hp : ∃ τ : E, p RatFunc.X = algebraMap E F τ)
    (ht : (D₀) (Fin.last 3) (p RatFunc.X) ≠ 0)
    (t : F) (htrans : Transcendental E t) (x A : Fin 3 → E) (w B C : E)
    (hfirst : ∀ i : Fin 3, (x₀) i.castSucc = algebraMap E F (x i) + algebraMap E F (A i) * t)
    (hlast : (x₀) (Fin.last 3) = algebraMap E F w + algebraMap E F B * t + algebraMap E F C * t ^ 2) :
    ∃ D : Derivation K F F,
      (∀ c : E, D (algebraMap E F c) = 0) ∧ D (p RatFunc.X) = 0 ∧
      (∀ i : Fin 3, D ((x₀) i.castSucc) = algebraMap E F (A i)) ∧
      D = coordinateEuler (fun i => algebraMap E F (A i)) (transverseParameterPartial (D₀) (p RatFunc.X)) ∧
      D ((x₀) (Fin.last 3)) = algebraMap E F B + 2 * algebraMap E F C * t ∧
      D (D ((x₀) (Fin.last 3))) = 2 * algebraMap E F C := by
  letI : CharZero E := charZero_of_injective_algebraMap (algebraMap K E).injective
  obtain ⟨Δ, _hΔt, hΔx, hΔw, hΔacc⟩ :=
    actual_parabolic_fiber_constructs_separating_derivation t htrans (x₀) x A w B C hfirst hlast
  let D : Derivation K F F := Δ.restrictScalars K
  have hconst (c : E) : D (algebraMap E F c) = 0 := Δ.map_algebraMap c
  have hDt : D (p RatFunc.X) = 0 := by obtain ⟨τ, hτ⟩ := hp; rw [hτ, hconst]
  exact ⟨D, hconst, hDt, hΔx,
    algebraic_source_fixed_parameter_direction_eq_transverse_frame (p RatFunc.X) ht D hDt _ hΔx,
    hΔw, hΔacc⟩

end DimensionFourDependence
