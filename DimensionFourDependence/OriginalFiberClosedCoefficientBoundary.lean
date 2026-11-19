import DimensionFourDependence.ActualFullFiberBoundary
import DimensionFourDependence.ActualBoundaryGraphDirection
import DimensionFourDependence.ProjectiveNormalizedPrimeCoordinates
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure

/-! # The actual original fiber has a normalized boundary over specified closed coefficients -/

namespace DimensionFourDependence

open MvPolynomial

attribute [local instance] coefficientFieldScalarTower MvPolynomial.gradedAlgebra

universe u

set_option maxHeartbeats 3000000
set_option synthInstance.maxHeartbeats 100000
set_option quotPrecheck false

variable {K : Type u} [Field K] [CharZero K]
  (H : Fin 4 → MvPolynomial (Fin 4) K) (hN : IsNilpotent (jac H))
  (hrank : polyRank (jac H) = 3) (p : Equiv.Perm (Fin 4))
  (hY : AlgebraicIndependent K (fun i : Fin 3 => algebraMap (MvPolynomial (Fin 4) K)
    (FractionRing (MvPolynomial (Fin 4) K)) (H (p i.castSucc))))

local notation "S₀" => FractionRing (MvPolynomial (Fin 4) K)
local notation "Y" => fun i : Fin 3 => algebraMap (MvPolynomial (Fin 4) K) S₀ (H (p i.castSucc))
local notation "L" => coefficientField (K := K) (Y)
local notation "x" => rationalCoordinate (K := K) (n := 4)

include hN hrank

/-- Every specified algebraically closed extension of the original
fiber coefficients contains a normalized actual boundary point in the
same original source chart. The valuation and residue embedding are constructed. -/
theorem actual_full_fiber_normalized_boundary_in_closed_coefficients
    (h c : L) (hc : (c : S₀) = firstFiberInvariantInChart p (Y) hY h)
    (B : Type u) [Field B] [Algebra (L) B] [IsAlgClosed B] :
    ∃ (z : Option (Fin 4) → B) (hz : z ≠ 0),
      projectiveFieldPoint (E := L) z hz ∈ projectiveClosureSet («L» := L) (x) ∧
      z none = 0 ∧ (fun i : Fin 3 => z (some (p i.castSucc))) ≠ 0 ∧
      ∃ j : Fin 4, z (some j) = 1 := by
  obtain ⟨V, j, hV, hpole⟩ := actual_fiber_chart_has_coordinate_valuation_pole H hN hrank p hY h c hc
  letI : Algebra (L) V := valuationConstantAlgebra V hV
  letI : IsScalarTower (L) V S₀ := valuationConstantScalarTower V hV
  obtain ⟨i, s, z, hz0, hz, hr0, hr1⟩ := exists_valuation_infinity_coordinates V (x) (p j.castSucc) hpole
  let κ := IsLocalRing.ResidueField V
  letI : Algebra.IsAlgebraic (L) κ := normalized_curve_boundary_residue_isAlgebraic
    V (x) i s z hz0 hz hr0 hr1 (actual_fiber_chart_source_trdeg_one H hN hrank p hY).le
  let v : Option (Fin 4) → κ := fun k => IsLocalRing.residue V (z k)
  have hv : v ≠ 0 := by
    intro hv
    have hi := congrFun hv (some i)
    change IsLocalRing.residue V (z (some i)) = 0 at hi
    exact one_ne_zero (hr1.symm.trans hi)
  have hpoint : projectiveFieldPoint (E := L) v hv ∈ projectiveClosureSet («L» := L) (x) := by
    apply residue_field_point_mem_projective_closure (IsScalarTower.toAlgHom (L) V κ)
      (show Function.Injective (algebraMap V S₀) from Subtype.val_injective) (x) s z _ hv
    intro k
    cases k with
    | none =>
      change (z none : S₀) = s * 1
      rw [mul_one]
      exact hz0
    | some k =>
      change (z (some k) : S₀) = s * (x) k
      exact hz k
  let φ : κ →ₐ[L] B := IsAlgClosed.lift
  let vB : Option (Fin 4) → B := fun k => φ (v k)
  have hvB : vB ≠ 0 := projective_coordinate_map_ne_zero φ v hv
  have hpointB : projectiveFieldPoint (E := L) vB hvB ∈ projectiveClosureSet («L» := L) (x) := by
    rw [projectiveFieldPoint_map_algHom φ v hv]
    exact hpoint
  have hzero : vB none = 0 := by change φ (IsLocalRing.residue V (z none)) = 0; rw [hr0, map_zero]
  have hi : vB (some i) = 1 := by change φ (IsLocalRing.residue V (z (some i))) = 1; rw [hr1, map_one]
  have hnonzero : (fun k => vB (some k)) ≠ 0 := by
    intro hn
    exact one_ne_zero (hi.symm.trans (congrFun hn i))
  exact ⟨vB, hvB, hpointB, hzero,
    actual_full_fiber_boundary_first_three_direction_ne_zero H p hY h c hc B
      vB hvB hnonzero hpointB hzero, i, hi⟩

end DimensionFourDependence
