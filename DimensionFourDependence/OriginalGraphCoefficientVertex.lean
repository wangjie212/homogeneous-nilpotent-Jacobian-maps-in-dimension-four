import DimensionFourDependence.OriginalGraphRootVertex
import DimensionFourDependence.OriginalGraphRootCoefficientData

/-! # The finite original graph coefficients supply the actual fixed vertex at infinity -/

namespace DimensionFourDependence

open MvPolynomial Matrix

attribute [local instance] coefficientFieldScalarTower

universe u

set_option quotPrecheck false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 100000
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

variable {K : Type u} [baseField : Field K] [baseChar : CharZero K] [IsAlgClosed K]
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

variable (κ : Type u) [targetField : Field κ] [targetBase : Algebra K κ]
    [targetCoeff : Algebra (coefficientField (K := K) (fun i : Fin 3 =>
      algebraMap (MvPolynomial (Fin 4) K) (FractionRing (MvPolynomial (Fin 4) K))
        (H (p i.castSucc)))) κ]
    [targetTower : IsScalarTower K (coefficientField (K := K) (fun i : Fin 3 =>
      algebraMap (MvPolynomial (Fin 4) K) (FractionRing (MvPolynomial (Fin 4) K))
        (H (p i.castSucc)))) κ]

local notation "gκ" => IsScalarTower.toAlgHom K (L) κ

variable [targetAlgebraic : Algebra.IsAlgebraic (coefficientField (K := K) (fun i : Fin 3 =>
      algebraMap (MvPolynomial (Fin 4) K) (FractionRing (MvPolynomial (Fin 4) K))
        (H (p i.castSucc)))) κ]

/-- The same finite original graph coefficients place the original
fourth-axis point in the actual full-fiber closure. -/
theorem finite_independent_original_graph_coefficient_data_construct_vertex_boundary
    (hrank : polyRank (jac H) = 3) (hN : IsNilpotent (jac H)) (hd1 : 1 < d)
    (hvertex : rationalImageNormal H I.equation (Fin.last 3) = 0)
    (c q k : L) (hc : (c : S₀) = firstFiberInvariantInChart p (Y) hY h)
    (hq : (q : S₀) = secondFiberInvariant p (Y) hY h c)
    (hk : (k : S₀) = thirdFiberInvariant p (Y) hY h c q)
    (hdata : FiniteIndependentOriginalGraphCoefficientData H I p hY h hh hH e hd hind hGauss κ c)
    (z : Option (Fin 4) → κ) (hz : z ≠ 0)
    (hpoint : projectiveFieldPoint (E := L) z hz ∈ projectiveClosureSet («L» := L) (x))
    (hz0 : z none = 0) (j : Fin 4) (hj : z (some j) = 1) :
    fourthAxisAffineInfinityPoint (L) ∈ projectiveClosureSet («L» := L) (x) := by
  let g := IsScalarTower.toAlgHom K (L) κ
  obtain ⟨E, hfin, hforms⟩ := hdata
  let coefficientType : Type u := E
  let coefficientFieldInstance : Field coefficientType := inferInstance
  let coefficientResidueAlgebra : Algebra coefficientType κ := inferInstance
  let finiteParameter : Module.Finite (g.comp ((a).comp e.toAlgHom)).fieldRange coefficientType := hfin
  let coefficientAlgebra : Algebra C₀ coefficientType := parameterImageFiniteExtensionAlgebra (a) e g E
  let finiteCoefficient : Module.Finite C₀ coefficientType := parameterImageFiniteExtensionAlgebra_finite (a) e g E
  let coefficientAlgebraic : Algebra.IsAlgebraic C₀ coefficientType := inferInstance
  have hcompat := parameterImageFiniteExtensionAlgebra_target_tower (a) e g E
  let hboundary := @independent_original_graph_root_forms_construct_original_vertex_boundary
    K baseField baseChar H I p hY h hh coefficientType coefficientFieldInstance
      coefficientAlgebra coefficientAlgebraic d hH hd hind hGauss e κ targetField
      targetBase targetCoeff targetTower coefficientResidueAlgebra targetAlgebraic
      hrank hN hd1 hvertex hcompat c q k hc hq hk hforms
      z hz hpoint hz0 j hj
  exact hboundary

end DimensionFourDependence
