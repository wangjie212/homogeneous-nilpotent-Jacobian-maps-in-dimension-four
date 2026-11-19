import DimensionFourDependence.ConstructedConeRootSlope
import DimensionFourDependence.AmbientDerivation
import DimensionFourDependence.AffineConeVertexDifferential

/-! # Every actual fiber derivation has the original source-coordinate chain rule

The original coordinate partials extend uniquely through algebraic source
extension. Every ambient derivation is their linear combination with its
actual coordinate values. A direction fixing a vertex-dependent parameter
is consequently exactly the transverse parameter-frame direction.
-/

namespace DimensionFourDependence

open MvPolynomial Matrix

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

/-- An ambient derivation on an actual algebraic source extension
is determined by its values on the original four source coordinates. -/
theorem algebraic_source_derivation_zero_of_original_coordinates
    (D : Derivation K F F) (hx : ∀ i : Fin 4, D ((x₀) i) = 0) : D = 0 := by
  have hpoly (P : MvPolynomial (Fin 4) K) :
      D (algebraMap S₀ F (algebraMap (MvPolynomial (Fin 4) K) S₀ P)) = 0 := by
    have he := comp_aeval_apply (rationalCoordinate (K := K) (n := 4))
      (IsScalarTower.toAlgHom K S₀ F) P
    rw [rationalCoordinate_aeval] at he
    change algebraMap S₀ F (algebraMap (MvPolynomial (Fin 4) K) S₀ P) = aeval (x₀) P at he
    rw [he]
    exact derivation_aeval_zero_of_coordinates D (x₀) hx P
  have hbase (s : S₀) : D (algebraMap S₀ F s) = 0 := by
    obtain ⟨P, Q, _hQ, rfl⟩ := IsFractionRing.div_surjective (A := MvPolynomial (Fin 4) K) s
    rw [map_div₀, D.leibniz_div, hpoly, hpoly]
    simp
  let : CharZero S₀ := charZero_of_injective_algebraMap (algebraMap K S₀).injective
  apply ambient_derivation_extension_unique (E := S₀) D 0
  · intro s
    simpa only [Derivation.zero_apply] using hbase s
  · exact Algebra.IsAlgebraic.isAlgebraic

/-- Every actual ambient derivation has the full chain rule in the
uniquely extended original coordinate partials. -/
theorem algebraic_source_derivation_coordinate_chain_rule
    (D : Derivation K F F) (u : F) :
    D u = ∑ i : Fin 4, D ((x₀) i) * (D₀) i u := by
  let Γ : Derivation K F F := ∑ i : Fin 4, D ((x₀) i) • (D₀) i
  have hΓ (j : Fin 4) : Γ ((x₀) j) = D ((x₀) j) := by
    simp [Γ, _root_.sum_apply, Derivation.smul_apply, algebraicPartial_coordinate, apply_ite, smul_eq_mul]
  have hz : D - Γ = 0 := algebraic_source_derivation_zero_of_original_coordinates (D - Γ)
    (fun i => by rw [Derivation.sub_apply, hΓ, sub_self])
  have he : D = Γ := sub_eq_zero.mp hz
  calc
    D u = Γ u := congrArg (fun e : Derivation K F F => e u) he
    _ = _ := by simp only [Γ, _root_.sum_apply, Derivation.smul_apply, smul_eq_mul]

/-- A genuinely occurring parameter and the three transverse source
coordinates determine every ambient derivation on the actual source. -/
theorem algebraic_source_parameter_transverse_derivation_ext
    (t : F) (ht : (D₀) (Fin.last 3) t ≠ 0) (D E : Derivation K F F)
    (hparam : D t = E t) (hx : ∀ i : Fin 3, D ((x₀) i.castSucc) = E ((x₀) i.castSucc)) : D = E := by
  let Δ := D - E
  have hΔt : Δ t = 0 := by simp only [Δ, Derivation.sub_apply, hparam, sub_self]
  have hΔx (i : Fin 3) : Δ ((x₀) i.castSucc) = 0 := by simp only [Δ, Derivation.sub_apply, hx, sub_self]
  have he := algebraic_source_derivation_coordinate_chain_rule Δ t
  simp only [hΔt, Fin.sum_univ_castSucc, hΔx, zero_mul, Finset.sum_const_zero, zero_add] at he
  have hlast : Δ ((x₀) (Fin.last 3)) = 0 := (mul_eq_zero.mp he.symm).resolve_right ht
  have hz : Δ = 0 := algebraic_source_derivation_zero_of_original_coordinates Δ (fun i => by
    refine Fin.lastCases hlast (fun i => hΔx i) i)
  exact sub_eq_zero.mp hz

/-- An actual fiber derivation fixing the source parameter is exactly
the constructed transverse parameter-frame direction with its actual
projected coordinate values. -/
theorem algebraic_source_fixed_parameter_direction_eq_transverse_frame
    (t : F) (ht : (D₀) (Fin.last 3) t ≠ 0) (D : Derivation K F F)
    (hDt : D t = 0) (A : Fin 3 → F) (hDx : ∀ i, D ((x₀) i.castSucc) = A i) :
    D = coordinateEuler A (transverseParameterPartial (D₀) t) := by
  let δ := transverseParameterPartial (D₀) t
  have hδt := (vertex_parameter_derivation_frame_parameter_values (D₀) t ht).2
  have hδx := (vertex_parameter_derivation_frame_coordinate_values (D₀) (x₀)
    (algebraicPartial_coordinate F) t).2.1
  apply algebraic_source_parameter_transverse_derivation_ext t ht
  · simp only [hDt, coordinateEuler_apply, hδt, mul_zero, Finset.sum_const_zero]
  · intro i
    rw [hDx]
    exact (coordinate_direction_coordinate δ (fun i : Fin 3 => (x₀) i.castSucc) A hδx i).symm

/-- The actual fiber derivative of every source function is its
fixed-parameter transverse gradient paired with the actual direction. -/
theorem algebraic_source_fixed_parameter_direction_apply
    (t : F) (ht : (D₀) (Fin.last 3) t ≠ 0) (D : Derivation K F F)
    (hDt : D t = 0) (A : Fin 3 → F) (hDx : ∀ i, D ((x₀) i.castSucc) = A i) (u : F) :
    D u = (fun i => transverseParameterPartial (D₀) t i u) ⬝ᵥ A := by
  rw [algebraic_source_fixed_parameter_direction_eq_transverse_frame t ht D hDt A hDx]
  exact coordinate_direction_apply_eq_gradient_pairing _ A u

end DimensionFourDependence

