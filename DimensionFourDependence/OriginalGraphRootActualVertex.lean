import DimensionFourDependence.OriginalGraphCoefficientVertex
import DimensionFourDependence.OriginalGraphRootCoefficientData
import DimensionFourDependence.OriginalMapIndependentGraphRootData
import DimensionFourDependence.FixedVertexGraphRootActualDegree
import DimensionFourDependence.OriginalMapSimpleRootLocalModel

/-! # The original valuation root witness constructs the original vertex at infinity -/

namespace DimensionFourDependence

open MvPolynomial Matrix

attribute [local instance] coefficientFieldScalarTower

universe u

set_option quotPrecheck false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 100000
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

variable {K : Type u} [Field K] [CharZero K] [IsAlgClosed K]
    (H : Fin 4 → MvPolynomial (Fin 4) K) (I : ImageRelationWitness H)
    (p : Equiv.Perm (Fin 4))
    (hY : AlgebraicIndependent K (fun i : Fin 3 => algebraMap (MvPolynomial (Fin 4) K)
      (FractionRing (MvPolynomial (Fin 4) K)) (H (p i.castSucc))))
    (h : coefficientField (K := K) (fun i : Fin 3 => algebraMap (MvPolynomial (Fin 4) K)
      (FractionRing (MvPolynomial (Fin 4) K)) (H (p i.castSucc))))
    (hh : (h : FractionRing (MvPolynomial (Fin 4) K)) = algebraMap (MvPolynomial (Fin 4) K)
      (FractionRing (MvPolynomial (Fin 4) K)) (H (p 3)))
    {d : ℕ} (hH : IsHomogMap H d) (e : RatFunc K ≃ₐ[K] closedGaussParameterField H I)
    (hd : 0 < d) (hind : ¬ComponentsDependent H) (hGauss : gaussImageDimension H I = 1)

local notation "S₀" => FractionRing (MvPolynomial (Fin 4) K)
local notation "C₀" => closedGaussParameterField H I
local notation "Y" => fun i : Fin 3 => algebraMap (MvPolynomial (Fin 4) K) S₀ (H (p i.castSucc))
local notation "L" => coefficientField (K := K) (Y)
local notation "x" => rationalCoordinate (K := K) (n := 4)
local notation "a" => actualClosedGaussCoefficientHom H I p hY h hh
local notation "A" => closedGaussCoefficientGraphSlope H I p hY h hh e
local notation "y₀" => coefficientCoordinate (K := K) (Y)
local notation "n₀" => parametricRulingDenominator (closedGaussCoefficientParameterHom H I p hY h hh e) (A) (y₀)

/-- The actual valuation root data place the original fourth axis in
the full-fiber closure, preserving the original chart and coefficient field. -/
theorem actual_finite_independent_graph_root_data_construct_original_vertex_boundary
    (hrank : polyRank (jac H) = 3) (hN : IsNilpotent (jac H)) (hd1 : 1 < d)
    (hvertex : rationalImageNormal H I.equation (Fin.last 3) = 0)
    (c q k : L) (hc : (c : S₀) = firstFiberInvariantInChart p (Y) hY h)
    (hq : (q : S₀) = secondFiberInvariant p (Y) hY h c)
    (hk : (k : S₀) = thirdFiberInvariant p (Y) hY h c q)
    (hdata : ActualFiniteIndependentGraphRootDataExists H I p hY h hh hH e hd hind hGauss c) :
    fourthAxisAffineInfinityPoint (L) ∈ projectiveClosureSet («L» := L) (x) := by
  obtain ⟨V, hV, hrest⟩ := hdata
  let : Algebra (L) V := valuationConstantAlgebra V hV
  let : IsScalarTower (L) V S₀ := valuationConstantScalarTower V hV
  let κ := IsLocalRing.ResidueField V
  let residueFieldInstance : Field κ := inferInstance
  let residueCoeffAlgebra : Algebra (L) κ := inferInstance
  let residueBaseAlgebra : Algebra K κ := ((algebraMap (L) κ).comp (algebraMap K (L))).toAlgebra
  let residueTower : IsScalarTower K (L) κ := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  obtain ⟨i, _scale, z, _hz0, _hz, hr0, hr1, hκalg, hres, hboundary, _hv,
    hcoeff⟩ := hrest
  let residueAlgebraic : Algebra.IsAlgebraic (L) κ := hκalg
  let hbound := @finite_independent_original_graph_coefficient_data_construct_vertex_boundary
    K inferInstance inferInstance inferInstance H I p hY h hh d hH e hd hind hGauss κ residueFieldInstance
      residueBaseAlgebra residueCoeffAlgebra residueTower residueAlgebraic
      hrank hN hd1 hvertex c q k hc hq hk hcoeff
      (fun j => IsLocalRing.residue V (z j)) hres hboundary hr0 i hr1
  exact hbound

end DimensionFourDependence
