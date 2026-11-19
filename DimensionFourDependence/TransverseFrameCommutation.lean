import DimensionFourDependence.AlgebraicSourceDerivationChain

/-! # The actual fixed-parameter source frame commutes -/

namespace DimensionFourDependence

open MvPolynomial

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 100000
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

variable {K F : Type*} [Field K] [CharZero K] [Field F] [Algebra K F]
    [Algebra (FractionRing (MvPolynomial (Fin 4) K)) F]
    [IsScalarTower K (FractionRing (MvPolynomial (Fin 4) K)) F]
    [Algebra.IsAlgebraic (FractionRing (MvPolynomial (Fin 4) K)) F]

local notation "S₀" => FractionRing (MvPolynomial (Fin 4) K)
local notation "x₀" => fun i : Fin 4 => algebraMap S₀ F (rationalCoordinate (K := K) i)
local notation "D₀" => algebraicPartial (K := K) F

/-- Two parameter-fixing derivations commute on the entire actual
algebraic source if their commutator kills its three transverse coordinates. -/
theorem algebraic_source_parameter_derivations_commute_of_coordinate_values
    (t : F) (ht : (D₀) (Fin.last 3) t ≠ 0) (D U : Derivation K F F)
    (hDt : D t = 0) (hUt : U t = 0)
    (hcoords : ∀ i : Fin 3, D (U ((x₀) i.castSucc)) = U (D ((x₀) i.castSucc))) :
    ∀ a : F, D (U a) = U (D a) := by
  have hz : ⁅D, U⁆ = 0 := by
    apply algebraic_source_parameter_transverse_derivation_ext t ht
    · simp only [Derivation.commutator_apply, hDt, hUt, map_zero, sub_self, Derivation.zero_apply]
    · intro i
      simp only [Derivation.commutator_apply, hcoords, sub_self, Derivation.zero_apply]
  intro a
  have he := congrArg (fun Δ : Derivation K F F => Δ a) hz
  simpa only [Derivation.commutator_apply, Derivation.zero_apply, sub_eq_zero] using he

/-- The constructed actual transverse coordinate partials commute,
without an assumed algebraic coordinate inverse or commuting-frame hypothesis. -/
theorem algebraic_source_transverse_parameter_partials_commute
    (t : F) (ht : (D₀) (Fin.last 3) t ≠ 0) (i j : Fin 3) :
    ∀ a : F, transverseParameterPartial (D₀) t i (transverseParameterPartial (D₀) t j a) =
      transverseParameterPartial (D₀) t j (transverseParameterPartial (D₀) t i a) := by
  have hparam := (vertex_parameter_derivation_frame_parameter_values (D₀) t ht).2
  have hcoord := (vertex_parameter_derivation_frame_coordinate_values (D₀) (x₀)
    (algebraicPartial_coordinate F) t).2.1
  apply algebraic_source_parameter_derivations_commute_of_coordinate_values t ht _ _ (hparam i) (hparam j)
  intro k
  rw [hcoord, hcoord]
  split_ifs <;> simp

/-- A direction with parameter-algebraic coordinates commutes with
every constructed transverse coordinate partial on the entire actual source. -/
theorem parameter_algebraic_direction_commutes_transverse_partials
    (p : RatFunc K →ₐ[K] F) (ht : (D₀) (Fin.last 3) (p RatFunc.X) ≠ 0)
    (V : Fin 3 → F) (hV : ∀ i, IsAlgebraic p.fieldRange (V i)) (j : Fin 3) :
    ∀ a : F, coordinateEuler V (transverseParameterPartial (D₀) (p RatFunc.X))
      (transverseParameterPartial (D₀) (p RatFunc.X) j a) =
        transverseParameterPartial (D₀) (p RatFunc.X) j
          (coordinateEuler V (transverseParameterPartial (D₀) (p RatFunc.X)) a) := by
  let δ := transverseParameterPartial (D₀) (p RatFunc.X)
  let U := coordinateEuler V δ
  have hparam := (vertex_parameter_derivation_frame_parameter_values (D₀) (p RatFunc.X) ht).2
  have hcoord := (vertex_parameter_derivation_frame_coordinate_values (D₀) (x₀)
    (algebraicPartial_coordinate F) (p RatFunc.X)).2.1
  have hUt : U (p RatFunc.X) = 0 := by
    simp only [U, δ, coordinateEuler_apply, hparam, mul_zero, Finset.sum_const_zero]
  have hUx (i : Fin 3) : U ((x₀) i.castSucc) = V i :=
    coordinate_direction_coordinate δ (fun i : Fin 3 => (x₀) i.castSucc) V hcoord i
  apply algebraic_source_parameter_derivations_commute_of_coordinate_values (p RatFunc.X) ht U (δ j) hUt (hparam j)
  intro i
  rw [hUx, transverse_parameter_partial_kills_algebraic_coefficient (D₀) p ht _ (hV i), hcoord]
  split_ifs <;> simp

/-- A parameter-algebraic direction fixing a function also fixes
all its transverse source derivatives. -/
theorem parameter_algebraic_direction_fixes_transverse_gradient
    (p : RatFunc K →ₐ[K] F) (ht : (D₀) (Fin.last 3) (p RatFunc.X) ≠ 0)
    (V : Fin 3 → F) (hV : ∀ i, IsAlgebraic p.fieldRange (V i))
    (a : F) (ha : coordinateEuler V (transverseParameterPartial (D₀) (p RatFunc.X)) a = 0) :
    ∀ j : Fin 3, coordinateEuler V (transverseParameterPartial (D₀) (p RatFunc.X))
      (transverseParameterPartial (D₀) (p RatFunc.X) j a) = 0 := by
  intro j
  rw [parameter_algebraic_direction_commutes_transverse_partials p ht V hV j, ha, map_zero]

end DimensionFourDependence
