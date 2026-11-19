import DimensionFourDependence.FiniteGaussBoundaryBranch
import DimensionFourDependence.ActualGaussBoundaryAcceleration

/-! # The original map constructs a finite Gauss-algebraic boundary branch

The actual curve valuation supplies a normalized boundary in all four
original coordinates. Its Gauss-field algebraicity, finite ruling-point
lift and zero acceleration follow from the checked generic-point
exclusion and actual invariant equations. The original map then supplies
its own chart, nonzero first invariant and closed-cover parameter.
-/

namespace DimensionFourDependence

open MvPolynomial Matrix

attribute [local instance] coefficientFieldScalarTower

universe u

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 100000
set_option quotPrecheck false

variable {K : Type u} [Field K] [CharZero K]
    (H : Fin 4 → MvPolynomial (Fin 4) K) (hrank : polyRank (jac H) = 3)
    (I : ImageRelationWitness H) (p : Equiv.Perm (Fin 4))
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
local notation "x" => rationalCoordinate (K := K) (n := 4)
local notation "M" => projectiveRatioField (K := K)
  (rationalImageNormal H I.equation) (imageNormalPivot H I)
local notation "f₀" => closedGaussCoefficientParameterHom H I p hY h hh e
local notation "A₀" => closedGaussCoefficientGraphSlope H I p hY h hh e
local notation "n₀" => parametricRulingDenominator (f₀) (A₀) (coefficientCoordinate (K := K) (Y))

/-- An actual normalized boundary of the original generic fiber,
algebraic over the original Gauss parameter, with a finite ruling-point
lift and the actual zero acceleration equation in the residue field. -/
noncomputable def ActualFiniteGaussBoundaryDirectionExists : Prop :=
  ∃ (V : ValuationSubring S₀) (hV : ∀ a : L, (a : S₀) ∈ V),
    letI : Algebra (L) V := valuationConstantAlgebra V hV
    letI : IsScalarTower (L) V S₀ := valuationConstantScalarTower V hV
    let κ := IsLocalRing.ResidueField V
    letI : Algebra K κ := ((algebraMap (L) κ).comp (algebraMap K (L))).toAlgebra
    letI : IsScalarTower K (L) κ := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
    ∃ (i : Fin 4) (s : S₀) (z : Option (Fin 4) → V),
      (z none : S₀) = s ∧ (∀ j, (z (some j) : S₀) = s * (x) j) ∧
      IsLocalRing.residue V (z none) = 0 ∧ IsLocalRing.residue V (z (some i)) = 1 ∧
      ∃ hκalg : Algebra.IsAlgebraic (L) κ,
      letI : Algebra.IsAlgebraic (L) κ := hκalg
      ∃ hres : (fun j => IsLocalRing.residue V (z j)) ≠ 0,
        projectiveFieldPoint (E := L) (fun j => IsLocalRing.residue V (z j)) hres ∈
          projectiveClosureSet («L» := L) (x) ∧
        (∀ j, IsAlgebraic (actualBoundaryOriginalGaussField H hrank p hY I κ)
          (IsLocalRing.residue V (z (some j)))) ∧
        coordinateEuler (fun j => IsLocalRing.residue V (z (some (p j.castSucc))))
          (extendedCoefficientPartial (Y) hY κ)
          (coordinateEuler (fun j => IsLocalRing.residue V (z (some (p j.castSucc))))
            (extendedCoefficientPartial (Y) hY κ) (algebraMap (L) κ ((n₀) * c))) = 0 ∧
        ∃ e₀ : RatFunc K ≃ₐ[K] projectiveRatioField (K := K)
          (rationalImageNormal H I.equation) (imageNormalPivot H I),
          Module.finrank (M) (LinearMap.ker (actualGaussRulingMatrix H I e₀).toLin') = 2 ∧
          ∃ B : IntermediateField (actualBoundaryOriginalGaussField H hrank p hY I κ) κ,
            Module.Finite (actualBoundaryOriginalGaussField H hrank p hY I κ) B ∧
            ∃ v : Fin 4 → B, v i = 1 ∧ (∀ j, (v j : κ) = IsLocalRing.residue V (z (some j))) ∧
              (actualBoundaryOriginalGaussRulingMatrix H hrank p hY I κ e₀).map
                (algebraMap (actualBoundaryOriginalGaussField H hrank p hY I κ) B) *ᵥ v = 0

include hh

/-- Actual invariant coefficients construct the normalized original
boundary, its finite Gauss-field branch and zero acceleration. No
boundary point, valuation, Gauss algebraicity or fixed branch is supplied. -/
theorem actual_finite_gauss_boundary_direction_exists
    {d : ℕ} (hd : 0 < d) (hH : IsHomogMap H d) (hN : IsNilpotent (jac H))
    (hind : ¬ ComponentsDependent H) (hGauss : gaussImageDimension H I = 1)
    (q k : L) (hc : (c : S₀) = firstFiberInvariantInChart p (Y) hY h)
    (hq : (q : S₀) = secondFiberInvariant p (Y) hY h c)
    (hk : (k : S₀) = thirdFiberInvariant p (Y) hY h c q) :
    ActualFiniteGaussBoundaryDirectionExists H hrank I p hY h c hh e := by
  obtain ⟨V, hV, hrest⟩ := actual_full_fiber_boundary_with_primitive_cross_equations H hrank p hY
    hN h c hc 1 H hH (by funext i; simp)
  refine ⟨V, hV, ?_⟩
  let : Algebra (L) V := valuationConstantAlgebra V hV
  let : IsScalarTower (L) V S₀ := valuationConstantScalarTower V hV
  let κ := IsLocalRing.ResidueField V
  let : Algebra K κ := ((algebraMap (L) κ).comp (algebraMap K (L))).toAlgebra
  let : IsScalarTower K (L) κ := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  obtain ⟨i, s, z, hz0, hz, hr0, hr1, hκalg, hres, hboundary, _⟩ := hrest
  let : Algebra.IsAlgebraic (L) κ := hκalg
  have hb : (fun j => IsLocalRing.residue V (z (some j))) ≠ 0 := by
    intro he
    have hi := congrFun he i
    change IsLocalRing.residue V (z (some i)) = 0 at hi
    exact one_ne_zero (hr1.symm.trans hi)
  have halg := actual_full_fiber_boundary_coordinates_algebraic_over_original_gauss H hrank p hY
    hd hH hN hind I hGauss h c q hh hc hq κ (fun j => IsLocalRing.residue V (z j))
    hres hb hboundary hr0 i hr1
  refine ⟨i, s, z, hz0, hz, hr0, hr1, hκalg, hres, hboundary, halg, ?_, ?_⟩
  · exact actual_full_boundary_original_gauss_algebraic_zero_acceleration H hrank I p hY h c q k hh e
      hGauss hd hH hq hk (IsScalarTower.toAlgHom (L) V κ)
      (show Function.Injective (algebraMap V S₀) from Subtype.val_injective) s z hz0 hz hr0 halg
  · exact actual_full_fiber_boundary_has_finite_original_gauss_branch H hrank p hY I κ
      hd hH hN hind hGauss h c q hh hc hq (fun j => IsLocalRing.residue V (z j))
      hres hb hboundary hr0 i hr1

end DimensionFourDependence
