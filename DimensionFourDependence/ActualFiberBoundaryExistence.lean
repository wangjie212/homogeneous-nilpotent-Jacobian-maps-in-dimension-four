import DimensionFourDependence.FiberTangentVariation
import DimensionFourDependence.ValuationProjectiveBoundary

/-! # Constructing an actual generic fiber boundary in the original graph chart

The actual nonzero vertical derivation and the actual first-invariant
equation force one of the first three source coordinates to be
transcendental over the actual coefficient field. Its valuation pole
constructs a nonzero normalized residue boundary direction.
-/

namespace DimensionFourDependence

open Matrix MvPolynomial

attribute [local instance] MvPolynomial.gradedAlgebra

universe u

variable {K : Type u} [Field K] [CharZero K]

local notation "S₀" => FractionRing (MvPolynomial (Fin 4) K)

/-- A nonzero actual vertical tangent and the original first-invariant
equation force a transcendental coordinate in the first three source
slots of that same graph chart. No nonconstant coordinate is supplied. -/
theorem graph_chart_has_transcendental_coordinate_of_vertical_tangent
    (Y : Fin 3 → S₀) (hY : AlgebraicIndependent K Y) (p : Equiv.Perm (Fin 4))
    (h c : coefficientField (K := K) Y)
    (hc : (c : S₀) = firstFiberInvariantInChart p Y hY h)
    (u : Fin 4 → S₀) (hu : u ≠ 0) (hker : rationalJacobian Y *ᵥ u = 0) :
    ∃ i : Fin 3, Transcendental (coefficientField (K := K) Y)
      (rationalCoordinate (K := K) (p i.castSucc)) := by
  let L := coefficientField (K := K) Y
  let D := fiberTangentDerivation Y hY u hu hker
  by_contra hn
  have halg (i : Fin 3) : IsAlgebraic L (rationalCoordinate (K := K) (p i.castSucc)) := by
    by_contra hi
    exact hn ⟨i, hi⟩
  have hfirst (i : Fin 3) : D (rationalCoordinate (K := K) (p i.castSucc)) = 0 :=
    derivation_zero_of_isAlgebraic D _ (halg i)
  have hDc : D (c : S₀) = 0 := D.map_algebraMap c
  have hDgradient (i : Fin 3) : D (coefficientPartial Y hY i h : S₀) = 0 := D.map_algebraMap _
  have hs : D (∑ i : Fin 3, (coefficientPartial Y hY i h : S₀) *
      rationalCoordinate (K := K) (p i.castSucc)) = 0 := by
    rw [map_sum]
    apply Finset.sum_eq_zero
    intro i _
    rw [D.leibniz, hfirst, hDgradient, smul_zero, smul_zero, zero_add]
  have hlast : D (rationalCoordinate (K := K) (p 3)) = 0 := by
    have he := congrArg D hc
    rw [firstFiberInvariantInChart, map_sub, hDc, hs, sub_zero] at he
    exact he.symm
  apply hu
  funext j
  obtain ⟨i, rfl⟩ := p.surjective j
  refine Fin.lastCases ?_ (fun k => ?_) i
  · rw [show Fin.last 3 = (3 : Fin 4) from by decide]
    simpa only [D, fiberTangentDerivation_apply, sourceVectorDerivation_coordinate, Pi.zero_apply] using hlast
  · simpa only [D, fiberTangentDerivation_apply, sourceVectorDerivation_coordinate, Pi.zero_apply] using hfirst k

variable (H : Fin 4 → MvPolynomial (Fin 4) K)
    (hN : IsNilpotent (jac H)) (hrank : polyRank (jac H) = 3) (p : Equiv.Perm (Fin 4))
    (hY : AlgebraicIndependent K (fun i : Fin 3 => algebraMap (MvPolynomial (Fin 4) K)
      (FractionRing (MvPolynomial (Fin 4) K)) (H (p i.castSucc))))
    (h c : coefficientField (K := K) (fun i : Fin 3 => algebraMap (MvPolynomial (Fin 4) K)
      (FractionRing (MvPolynomial (Fin 4) K)) (H (p i.castSucc))))
    (hc : (c : FractionRing (MvPolynomial (Fin 4) K)) = firstFiberInvariantInChart p
      (fun i : Fin 3 => algebraMap (MvPolynomial (Fin 4) K)
        (FractionRing (MvPolynomial (Fin 4) K)) (H (p i.castSucc))) hY h)

set_option quotPrecheck false

local notation "Y₀" => fun i : Fin 3 => algebraMap (MvPolynomial (Fin 4) K) S₀ (H (p i.castSucc))
local notation "L₀" => coefficientField (K := K) (Y₀)
local notation "x₀" => fun i : Fin 3 => rationalCoordinate (K := K) (p i.castSucc)

include hN hrank hc

/-- The original nilpotent map constructs the actual vertical tangent
and hence a transcendental first-three source coordinate over its actual
graph coefficient field. No tangent or coordinate choice is supplied. -/
theorem actual_fiber_chart_has_transcendental_source_coordinate :
    ∃ i : Fin 3, Transcendental (L₀) ((x₀) i) := by
  let Q : Fin 4 → S₀ := fun i => algebraMap (MvPolynomial (Fin 4) K) S₀ (H i)
  have hQN : IsNilpotent (rationalJacobian Q) := by
    rw [rationalJacobian_polynomial H]
    exact hN.map (algebraMap (MvPolynomial (Fin 4) K) S₀).mapMatrix
  have hQr : (rationalJacobian Q).rank = 3 := by
    rw [rationalJacobian_polynomial H]
    exact hrank
  obtain ⟨u, hu, hker⟩ := matrix_nilpotent_exists_nonzero_kernel _ hQN (by rw [hQr]; decide)
  apply graph_chart_has_transcendental_coordinate_of_vertical_tangent (Y₀) hY p h c hc u hu
  funext i
  exact congrFun hker (p i.castSucc)

/-- A pole of an actual original source coordinate is constructed
over the entire actual coefficient field, without algebraically closed
constants, a chosen valuation, or a chosen coordinate. -/
theorem actual_fiber_chart_has_coordinate_valuation_pole :
    ∃ (V : ValuationSubring S₀) (i : Fin 3),
      (∀ a : L₀, (a : S₀) ∈ V) ∧ 1 < V.valuation ((x₀) i) := by
  obtain ⟨i, hi⟩ := actual_fiber_chart_has_transcendental_source_coordinate H hN hrank p hY h c hc
  obtain ⟨V, hV, hpole⟩ := transcendental_has_valuation_pole_gt_one ((x₀) i) hi
  exact ⟨V, i, hV, hpole⟩

/-- The actual fiber constructs its own nonzero normalized residue
direction: the homogenizing coordinate is zero and an original affine
coordinate is one. The valuation contains the entire coefficient field. -/
theorem actual_fiber_chart_has_nonzero_residue_boundary_coordinates :
    ∃ (V : ValuationSubring S₀), (∀ a : L₀, (a : S₀) ∈ V) ∧
      ∃ (i : Fin 3) (s : S₀) (z : Option (Fin 3) → V),
        (z none : S₀) = s ∧ (∀ j, (z (some j) : S₀) = s * (x₀) j) ∧
        IsLocalRing.residue V (z none) = 0 ∧ IsLocalRing.residue V (z (some i)) = 1 := by
  obtain ⟨V, i, hV, hpole⟩ := actual_fiber_chart_has_coordinate_valuation_pole H hN hrank p hY h c hc
  obtain ⟨j, s, z, hz⟩ := exists_valuation_infinity_coordinates V (x₀) i hpole
  exact ⟨V, hV, j, s, z, hz⟩

/-- The actual graph-chart generic fiber meets infinity in its actual
projective closure over its original coefficient field. No geometric
boundary point or algebraically closed coefficient field is assumed. -/
theorem actual_fiber_chart_has_projective_boundary :
    ∃ q : ProjectiveSpectrum (homogeneousSubmodule (Option (Fin 3)) (L₀)),
      q ∈ projectiveClosureSet (L := L₀) (x₀) ∧
      q ∈ ProjectiveSpectrum.zeroLocus (homogeneousSubmodule (Option (Fin 3)) (L₀)) {X none} := by
  obtain ⟨V, i, hV, hpole⟩ := actual_fiber_chart_has_coordinate_valuation_pole H hN hrank p hY h c hc
  exact coordinate_pole_has_projective_boundary V hV (x₀) i hpole

end DimensionFourDependence
