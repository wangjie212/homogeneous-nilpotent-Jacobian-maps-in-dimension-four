import DimensionFourDependence.PrimitiveBoundaryImage
import DimensionFourDependence.ActualFiberBoundaryResidue
import DimensionFourDependence.GenericFiberOutput
import DimensionFourDependence.ProjectiveLineAtlasPoints

/-! # An actual boundary in all four original source coordinates

The original curve valuation supplies a normalized four-coordinate
direction. Its projective point belongs to the actual full fiber
closure and satisfies the primitive-map target cross equations.
-/

namespace DimensionFourDependence

open MvPolynomial Matrix

attribute [local instance] coefficientFieldScalarTower MvPolynomial.gradedAlgebra

universe u

set_option quotPrecheck false
set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 100000

variable {K : Type u} [Field K] [CharZero K]
    (H : Fin 4 → MvPolynomial (Fin 4) K) (hrank : polyRank (jac H) = 3)
    (p : Equiv.Perm (Fin 4))
    (hY : AlgebraicIndependent K (fun i : Fin 3 => algebraMap (MvPolynomial (Fin 4) K)
      (FractionRing (MvPolynomial (Fin 4) K)) (H (p i.castSucc))))

local notation "S₀" => FractionRing (MvPolynomial (Fin 4) K)
local notation "Y" => fun i : Fin 3 => algebraMap (MvPolynomial (Fin 4) K) S₀ (H (p i.castSucc))
local notation "L" => coefficientField (K := K) (Y)
local notation "x" => rationalCoordinate (K := K) (n := 4)

/-- All four original output values, as actual elements of the
selected graph coefficient field. Membership follows from rank three. -/
noncomputable def actualChartOutputCoordinate (i : Fin 4) : L :=
  ⟨algebraMap (MvPolynomial (Fin 4) K) S₀ (H i),
    fullOutputField_mem_coefficientField
      (fun j => algebraMap (MvPolynomial (Fin 4) K) S₀ (H j))
      (by rw [rationalJacobian_polynomial H]; exact hrank) p hY
      (fullOutputCoordinate (K := K) (fun j => algebraMap (MvPolynomial (Fin 4) K) S₀ (H j)) i)⟩

theorem actualChartOutputCoordinate_source (i : Fin 4) :
    algebraMap (L) S₀ (actualChartOutputCoordinate H hrank p hY i) =
      algebraMap (MvPolynomial (Fin 4) K) S₀ (H i) := rfl

theorem actualChartOutputCoordinate_ne_zero :
    actualChartOutputCoordinate H hrank p hY ≠ 0 := by
  intro hz
  apply rank_three_polynomial_map_ne_zero H hrank
  funext i
  change H i = 0
  apply IsFractionRing.injective (MvPolynomial (Fin 4) K) S₀
  have he := congrArg (algebraMap (L) S₀) (congrFun hz i)
  simpa only [actualChartOutputCoordinate_source, Pi.zero_apply, map_zero] using he

/-- The actual full source evaluates the coefficient-extended map to
its original four output constants. -/
theorem actualChartOutputCoordinate_fiber_evaluation (i : Fin 4) :
    aeval (x) (MvPolynomial.map (algebraMap K (L)) (H i)) =
      algebraMap (L) S₀ (actualChartOutputCoordinate H hrank p hY i) := by
  rw [aeval_map_algebra_extension, actualChartOutputCoordinate_source]
  have he := aeval_polynomial_to_fraction (fun j : Fin 4 => (X j : MvPolynomial (Fin 4) K)) (H i)
  simp only [aeval_X_left_apply] at he
  exact he.symm

/-- The original actual fiber constructs a normalized nonzero
four-coordinate boundary point, algebraic residue field over its full
coefficient field, and every original primitive-map target cross equation.
No valuation, full-coordinate lift, boundary point or cross equation is
supplied as an auxiliary datum. -/
theorem actual_full_fiber_boundary_with_primitive_cross_equations
    (hN : IsNilpotent (jac H)) (h c : L)
    (hc : (c : S₀) = firstFiberInvariantInChart p (Y) hY h)
    (g : MvPolynomial (Fin 4) K) (P : Fin 4 → MvPolynomial (Fin 4) K)
    {D : ℕ} (hP : IsHomogMap P D) (hHP : H = fun i => g * P i) :
    ∃ (V : ValuationSubring S₀) (hV : ∀ a : L, (a : S₀) ∈ V),
      letI : Algebra (L) V := valuationConstantAlgebra V hV
      letI : IsScalarTower (L) V S₀ := valuationConstantScalarTower V hV
      ∃ (i : Fin 4) (s : S₀) (z : Option (Fin 4) → V),
        (z none : S₀) = s ∧ (∀ j, (z (some j) : S₀) = s * (x) j) ∧
        IsLocalRing.residue V (z none) = 0 ∧ IsLocalRing.residue V (z (some i)) = 1 ∧
        Algebra.IsAlgebraic (L) (IsLocalRing.ResidueField V) ∧
        ∃ hres : (fun j => IsLocalRing.residue V (z j)) ≠ 0,
          projectiveFieldPoint (E := L) (fun j => IsLocalRing.residue V (z j)) hres ∈
            projectiveClosureSet («L» := L) (x) ∧
          ∀ j k, algebraMap (L) (IsLocalRing.ResidueField V) (actualChartOutputCoordinate H hrank p hY j) *
              aeval (fun l => IsLocalRing.residue V (z (some l)))
                (MvPolynomial.map (algebraMap K (L)) (P k)) -
            algebraMap (L) (IsLocalRing.ResidueField V) (actualChartOutputCoordinate H hrank p hY k) *
              aeval (fun l => IsLocalRing.residue V (z (some l)))
                (MvPolynomial.map (algebraMap K (L)) (P j)) = 0 := by
  obtain ⟨V, j, hV, hpole⟩ := actual_fiber_chart_has_coordinate_valuation_pole H hN hrank p hY h c hc
  obtain ⟨i, s, z, hz0, hz, hr0, hr1⟩ := exists_valuation_infinity_coordinates V (x) (p j.castSucc) hpole
  refine ⟨V, hV, ?_⟩
  let : Algebra (L) V := valuationConstantAlgebra V hV
  let : IsScalarTower (L) V S₀ := valuationConstantScalarTower V hV
  refine ⟨i, s, z, hz0, hz, hr0, hr1, ?_, ?_⟩
  · exact normalized_curve_boundary_residue_isAlgebraic V (x) i s z hz0 hz hr0 hr1
      (actual_fiber_chart_source_trdeg_one H hN hrank p hY).le
  · have hres : (fun j => IsLocalRing.residue V (z j)) ≠ 0 := by
      intro he
      have hi := congrFun he (some i)
      rw [hr1] at hi
      exact one_ne_zero hi
    have hboundary : projectiveFieldPoint (E := L) (fun j => IsLocalRing.residue V (z j)) hres ∈
        projectiveClosureSet («L» := L) (x) := by
      apply residue_field_point_mem_projective_closure (IsScalarTower.toAlgHom (L) V (IsLocalRing.ResidueField V))
        (show Function.Injective (algebraMap V S₀) from Subtype.val_injective) (x) s z _ hres
      intro j
      cases j with
      | none =>
          change (z none : S₀) = s * 1
          rw [mul_one]
          exact hz0
      | some j => exact hz j
    refine ⟨hres, hboundary, ?_⟩
    apply primitive_boundary_cross_equations
      (fun j => MvPolynomial.map (algebraMap K (L)) (H j))
      (fun j => MvPolynomial.map (algebraMap K (L)) (P j))
      (MvPolynomial.map (algebraMap K (L)) g) (fun j => (hP j).map (algebraMap K (L)))
      (by funext j; rw [congrFun hHP j, map_mul]) (x)
      (actualChartOutputCoordinate H hrank p hY) (actualChartOutputCoordinate_ne_zero H hrank p hY)
      (actualChartOutputCoordinate_fiber_evaluation H hrank p hY) _ hres hboundary

end DimensionFourDependence
