import DimensionFourDependence.AffinePlaneCurveDichotomy
import DimensionFourDependence.Corollary53ScalarAction
import DimensionFourDependence.FixedCoordinateReduction
import DimensionFourDependence.LinearConjugacyRank

/-! # Corollary 5.3 in the original-field coordinates with zero final output -/

namespace DimensionFourDependence

open MvPolynomial Matrix

universe u
set_option maxHeartbeats 4300000
set_option synthInstance.maxHeartbeats 140000

variable {K : Type u} [Field K] [CharZero K]
local notation "R₄" => MvPolynomial (Fin 4) K
local notation "F" => FractionRing R₄
local notation "x" => (rationalCoordinate (K := K) (n := 4))

/-- The two geometric conclusions of Corollary 5.3 in a fixed source
chart, expressed on all actual minimal prime components. -/
def GenericFibersAreLinesOrConicsWithFreeScalars (H : Fin 4 → R₄) (d : ℕ) : Prop :=
  ∀ (E : Type u) [Field E] [IsAlgClosed E] [Algebra (polynomialOutputField H) E]
    [Algebra.IsAlgebraic (polynomialOutputField H) E] [Algebra K E]
    [IsScalarTower K (polynomialOutputField H) E],
    let I := extendCoefficientIdeal E (fiberVanishingIdeal (L := polynomialOutputField H) x)
    (∀ (P : Ideal (MvPolynomial (Fin 4) E)) [P.IsPrime], P ∈ I.minimalPrimes →
      LiesInAffineLine (E := E) (primeQuotientCoordinate P) ∨
        LiesOnAffinePlaneConic (E := E) (primeQuotientCoordinate P)) ∧
    ∃ action : MulAction (rootsOfUnity d E) I.minimalPrimes,
      letI := action
      (∀ (u : rootsOfUnity d E) (P : I.minimalPrimes),
        (u • P).val = P.val.comap (polynomialScalarEquiv (u : Eˣ)).toRingHom) ∧
      (∀ (u : rootsOfUnity d E) (P : I.minimalPrimes), u • P = P → u = 1) ∧
      d ∣ Nat.card I.minimalPrimes

theorem zero_last_output_generic_fibers_line_or_conic_with_free_scalars
    (H : Fin 4 → R₄) {d : ℕ} (hd : 0 < d) (hH : IsHomogMap H d)
    (hN : IsNilpotent (jac H)) (hr : polyRank (jac H) = 3) (h₀ : H (Fin.last 3) = 0) :
    GenericFibersAreLinesOrConicsWithFreeScalars H d := by
  intro E _ _ _ _ _ _
  dsimp only
  constructor
  · intro P _ hP
    let Y : Fin 4 → F := fun i => algebraMap R₄ F (H i)
    have hJ : rationalJacobian Y = (jac H).map (algebraMap R₄ F) := rationalJacobian_polynomial H
    have hRank : (rationalJacobian Y).rank = 3 := hJ.symm ▸ hr
    have hNil : IsNilpotent (rationalJacobian Y) := hJ.symm ▸ hN.map (algebraMap R₄ F).mapMatrix
    have hz : Y (Fin.last 3) = 0 := by simp only [Y, h₀, map_zero]
    obtain ⟨W⟩ := nilpotent_rank_three_zero_last_output_constructs_fiber_equations Y hNil hRank hz
    obtain ⟨V⟩ := fixed_last_geometric_component_constructs_affine_plane_chart Y W hNil hRank E P hP
    exact V.line_or_plane_conic
  · exact homogeneous_rank_three_zero_last_output_free_scalar_action (E := E) H hd hH hN hr h₀

/-- Corollary 5.3. The original field supplies inverse constant frames
with zero final output. In these coordinates every geometric generic
component is a line or a plane conic, and the actual scalar action is free. -/
theorem corollary_5_3
    (H : Fin 4 → R₄) {d : ℕ} (hd : 0 < d) (hH : IsHomogMap H d)
    (hN : IsNilpotent (jac H)) (hr : polyRank (jac H) = 3) :
    ∃ T S : Matrix (Fin 4) (Fin 4) K, T * S = 1 ∧ S * T = 1 ∧
      let G := linearPolynomialConjugate T S H
      G (Fin.last 3) = 0 ∧ GenericFibersAreLinesOrConicsWithFreeScalars G d := by
  obtain ⟨T, S, hTS, hST, hG⟩ := constant_relation_constructs_zero_component_conjugacy H
    (theorem_1_1 d hd H hH hN) (Fin.last 3)
  refine ⟨T, S, hTS, hST, hG, ?_⟩
  exact zero_last_output_generic_fibers_line_or_conic_with_free_scalars _ hd
    (linearPolynomialConjugate_homogeneous T S H hH)
    (linearPolynomialConjugate_nilpotent T S hTS hST H hN)
    ((linearPolynomialConjugate_polyRank T S hTS hST H).trans hr) hG

end DimensionFourDependence
