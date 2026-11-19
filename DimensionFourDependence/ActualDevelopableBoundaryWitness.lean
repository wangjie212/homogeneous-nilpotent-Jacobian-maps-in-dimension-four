import DimensionFourDependence.ActualFiberBoundaryExistence
import DimensionFourDependence.ActualFiberBoundaryResidue
import DimensionFourDependence.ActualDevelopableBoundaryEquation

/-! # A nonzero actual developable boundary direction is constructed

The original map supplies its own graph chart, invariant coefficients,
closed Gauss cover, valuation pole and normalized projective boundary
point. Ruling membership and the modified quadratic equation are derived.
Algebraicity over the Gauss parameter alone is not asserted here.
-/

namespace DimensionFourDependence

open MvPolynomial Matrix

attribute [local instance] coefficientFieldScalarTower MvPolynomial.gradedAlgebra

universe u

set_option quotPrecheck false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 100000

variable {K : Type u} [Field K] [CharZero K]
    (H : Fin 4 → MvPolynomial (Fin 4) K) (I : ImageRelationWitness H)
    (p : Equiv.Perm (Fin 4))
    (hY : AlgebraicIndependent K (fun i : Fin 3 => algebraMap (MvPolynomial (Fin 4) K)
      (FractionRing (MvPolynomial (Fin 4) K)) (H (p i.castSucc))))
    (h c : coefficientField (K := K) (fun i : Fin 3 => algebraMap (MvPolynomial (Fin 4) K)
      (FractionRing (MvPolynomial (Fin 4) K)) (H (p i.castSucc))))
    (hh : (h : FractionRing (MvPolynomial (Fin 4) K)) = algebraMap (MvPolynomial (Fin 4) K)
      (FractionRing (MvPolynomial (Fin 4) K)) (H (p 3)))
    (e : RatFunc K ≃ₐ[K] closedGaussParameterField H I)

local notation "S₀" => FractionRing (MvPolynomial (Fin 4) K)
local notation "Y" => fun i : Fin 3 => algebraMap (MvPolynomial (Fin 4) K) S₀ (H (p i.castSucc))
local notation "L" => coefficientField (K := K) (Y)
local notation "x₀" => fun i : Fin 3 => rationalCoordinate (K := K) (p i.castSucc)
local notation "f₀" => closedGaussCoefficientParameterHom H I p hY h hh e
local notation "A₀" => closedGaussCoefficientGraphSlope H I p hY h hh e
local notation "Λ₀" => parametricGraphCubicCovector (f₀) (A₀) (coefficientCoordinate (K := K) (Y))

/-- An actual nonzero normalized residue boundary point of the
original generic fiber, satisfying its actual ruling and modified
quadratic equations. The valuation contains the entire coefficient field. -/
noncomputable def ActualClosedGaussBoundaryDirectionExists : Prop :=
  ∃ (V : ValuationSubring S₀) (hV : ∀ a : L, (a : S₀) ∈ V),
    letI : Algebra (L) V := valuationConstantAlgebra V hV
    letI : IsScalarTower (L) V S₀ := valuationConstantScalarTower V hV
    ∃ (i : Fin 3) (s : S₀) (z : Option (Fin 3) → V),
      (z none : S₀) = s ∧ (∀ j, (z (some j) : S₀) = s * (x₀) j) ∧
      IsLocalRing.residue V (z none) = 0 ∧ IsLocalRing.residue V (z (some i)) = 1 ∧
      Algebra.IsAlgebraic (L) (IsLocalRing.ResidueField V) ∧
      Module.Finite (L) (IntermediateField.adjoin (L)
        (Set.range (fun j => IsLocalRing.residue V (z (some j))))) ∧
      ∃ hres : (fun j : Option (Fin 3) => IsLocalRing.residue V (z j)) ≠ 0,
        projectiveFieldPoint (E := L) (fun j => IsLocalRing.residue V (z j)) hres ∈
          projectiveClosureSet («L» := L) (x₀) ∧
        (fun j => algebraMap (L) (IsLocalRing.ResidueField V)
          ((f₀) (rationalParameterDerivative K ((A₀) j)))) ⬝ᵥ
            (fun j => IsLocalRing.residue V (z (some j))) = 0 ∧
        matrixBilinearPairing ((coefficientHessian (Y) hY c).map (algebraMap (L) (IsLocalRing.ResidueField V)))
          (fun j => IsLocalRing.residue V (z (some j))) (fun j => IsLocalRing.residue V (z (some j))) -
          (2 / 3 : IsLocalRing.ResidueField V) *
            ((fun j => algebraMap (L) (IsLocalRing.ResidueField V) ((Λ₀) j)) ⬝ᵥ
              (fun j => IsLocalRing.residue V (z (some j)))) *
            ((fun j => algebraMap (L) (IsLocalRing.ResidueField V) (coefficientPartial (Y) hY j c)) ⬝ᵥ
              (fun j => IsLocalRing.residue V (z (some j)))) = 0

/-- The original actual invariant equations construct the entire
boundary-direction witness, without a supplied valuation, boundary point,
ruling-membership condition or modified quadratic equation. -/
theorem actual_closed_gauss_boundary_direction_exists
    {d : ℕ} (hd : 0 < d) (hH : IsHomogMap H d)
    (hN : IsNilpotent (jac H)) (hrank : polyRank (jac H) = 3)
    (hGauss : gaussImageDimension H I = 1)
    (q k : L) (hc : (c : S₀) = firstFiberInvariantInChart p (Y) hY h)
    (hq : (q : S₀) = secondFiberInvariant p (Y) hY h c)
    (hk : (k : S₀) = thirdFiberInvariant p (Y) hY h c q) :
    ActualClosedGaussBoundaryDirectionExists H I p hY h c hh e := by
  obtain ⟨V, hV, i, s, z, hz0, hz, hr0, hr1⟩ :=
    actual_fiber_chart_has_nonzero_residue_boundary_coordinates H hN hrank p hY h c hc
  refine ⟨V, hV, ?_⟩
  let : Algebra (L) V := valuationConstantAlgebra V hV
  let : IsScalarTower (L) V S₀ := valuationConstantScalarTower V hV
  dsimp only
  refine ⟨i, s, z, hz0, hz, hr0, hr1,
    actual_fiber_chart_normalized_boundary_residue_isAlgebraic H hN hrank p hY V i s z hz0 hz hr0 hr1,
    actual_fiber_boundary_coordinate_field_finite H hN hrank p hY V i s z hz0 hz hr0 hr1, ?_⟩
  let κ := IsLocalRing.ResidueField V
  let π : V →ₐ[L] κ := IsScalarTower.toAlgHom (L) V κ
  have hres : (fun j => IsLocalRing.residue V (z j)) ≠ 0 := by
    intro he
    have hi := congrFun he (some i)
    change IsLocalRing.residue V (z (some i)) = 0 at hi
    exact one_ne_zero (hr1.symm.trans hi)
  refine ⟨hres, ?_, ?_, ?_⟩
  · apply residue_field_point_mem_projective_closure π
      (show Function.Injective (algebraMap V S₀) from Subtype.val_injective) (x₀) s z _ hres
    intro j
    cases j with
    | none =>
      change (z none : S₀) = s * 1
      simpa only [mul_one] using hz0
    | some j => exact hz j
  · exact actual_closed_gauss_quadratic_boundary_mem_ruling H I p hY h hh e hGauss hd hH
      c q hq π (show Function.Injective (algebraMap V S₀) from Subtype.val_injective)
      s z hz0 hz hr0
  · exact actual_closed_gauss_modified_cubic_boundary_equation H I p hY h hh e hGauss hd hH
      c q k hq hk π (show Function.Injective (algebraMap V S₀) from Subtype.val_injective)
      s z hz0 hz hr0

end DimensionFourDependence
