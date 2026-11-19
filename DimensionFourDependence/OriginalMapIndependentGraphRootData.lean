import DimensionFourDependence.OriginalGraphRootCoefficientData
import DimensionFourDependence.OriginalMapIndependentConeRootData
import DimensionFourDependence.NativeIndependentRootGraphTransfer

/-! # The original map constructs its exact independent graph invariant root equations -/

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

/-- The actual original valuation boundary and its same finite
parameter coefficient field carry the exact independent graph root
equations n(Y)c=m(Y)rho, rho^d=s(Y). Both original fourth-axis values
and independence on the original chosen ruling are retained. -/
noncomputable def ActualFiniteIndependentGraphRootDataExists (c : L) : Prop :=
  ∃ (V : ValuationSubring S₀) (hV : ∀ b : L, (b : S₀) ∈ V),
    let : Algebra (L) V := valuationConstantAlgebra V hV
    let : IsScalarTower (L) V S₀ := valuationConstantScalarTower V hV
    let κ := IsLocalRing.ResidueField V
    let : Algebra K κ := ((algebraMap (L) κ).comp (algebraMap K (L))).toAlgebra
    let : IsScalarTower K (L) κ := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
    ∃ (i : Fin 4) (scale : S₀) (z : Option (Fin 4) → V),
      (z none : S₀) = scale ∧ (∀ j, (z (some j) : S₀) = scale * (x) j) ∧
      IsLocalRing.residue V (z none) = 0 ∧ IsLocalRing.residue V (z (some i)) = 1 ∧
      ∃ hκalg : Algebra.IsAlgebraic (L) κ,
      let : Algebra.IsAlgebraic (L) κ := hκalg
      ∃ hres : (fun j => IsLocalRing.residue V (z j)) ≠ 0,
        projectiveFieldPoint (E := L) (fun j => IsLocalRing.residue V (z j)) hres ∈
          projectiveClosureSet («L» := L) (x) ∧
        (fun j : Fin 3 => IsLocalRing.residue V (z (some (p j.castSucc)))) ≠ 0 ∧
        FiniteIndependentOriginalGraphCoefficientData H I p hY h hh hH e hd hind hGauss κ c

/-- The same actual finite native witnesses construct the exact
original graph product and power equations in their retained
algebraic residue field. No graph root or product identity is supplied. -/
theorem actual_finite_independent_native_root_data_constructs_exact_graph_root_data
    (c : L) (hc : (c : S₀) = firstFiberInvariantInChart p (Y) hY h) (hc0 : c ≠ 0)
    (hdata : ActualFiniteIndependentConeRootDataExists H I p hY h hh hH e hd hind hGauss) :
    ActualFiniteIndependentGraphRootDataExists H I p hY h hh hH e hd hind hGauss c := by
  obtain ⟨V, hV, hrest⟩ := hdata
  refine ⟨V, hV, ?_⟩
  let : Algebra (L) V := valuationConstantAlgebra V hV
  let : IsScalarTower (L) V S₀ := valuationConstantScalarTower V hV
  let κ := IsLocalRing.ResidueField V
  let : Algebra K κ := ((algebraMap (L) κ).comp (algebraMap K (L))).toAlgebra
  let : IsScalarTower K (L) κ := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  obtain ⟨i, scale, z, hz0, hz, hr0, hr1, hκalg, hres, hboundary, hv, E, hfin, hnative⟩ := hrest
  let : Algebra.IsAlgebraic (L) κ := hκalg
  let g := IsScalarTower.toAlgHom K (L) κ
  refine ⟨i, scale, z, hz0, hz, hr0, hr1, hκalg, hres, hboundary, hv, E, hfin, ?_⟩
  let : Module.Finite (g.comp ((a).comp e.toAlgHom)).fieldRange E := hfin
  let : Algebra C₀ E := parameterImageFiniteExtensionAlgebra (a) e g E
  let : Module.Finite C₀ E := parameterImageFiniteExtensionAlgebra_finite (a) e g E
  let : Algebra.IsAlgebraic C₀ E := inferInstance
  have hcompat := parameterImageFiniteExtensionAlgebra_target_tower (a) e g E
  let hforms := independent_native_root_data_constructs_same_boundary_graph_root
    H I p hY h hh E hd hH hind hGauss e κ hcompat c hc hc0 hnative
  exact hforms

omit p hY h hh e hd in
/-- The original fixed-vertex nilpotent nonplanar rank-three map
constructs its own exact independent graph root data, including the
actual original boundary point, finite parameter field and algebraic
residue extension. No native or graph root hypotheses are supplied. -/
theorem original_fixed_vertex_map_constructs_exact_finite_independent_graph_root_data
    (hN : IsNilpotent (jac H)) (hrank : polyRank (jac H) = 3) (hd1 : 1 < d)
    (hvertex : rationalImageNormal H I.equation (Fin.last 3) = 0) :
    ∃ (p : Equiv.Perm (Fin 4))
      (hY : AlgebraicIndependent K (fun i : Fin 3 => algebraMap (MvPolynomial (Fin 4) K)
        S₀ (H (p i.castSucc))))
      (h c : coefficientField (K := K) (fun i : Fin 3 => algebraMap (MvPolynomial (Fin 4) K)
        S₀ (H (p i.castSucc))))
      (hh : (h : S₀) = algebraMap (MvPolynomial (Fin 4) K) S₀ (H (p 3)))
      (e : RatFunc K ≃ₐ[K] C₀),
      c ≠ 0 ∧ (c : S₀) = firstFiberInvariantInChart p
        (fun i : Fin 3 => algebraMap (MvPolynomial (Fin 4) K) S₀ (H (p i.castSucc))) hY h ∧
      ActualFiniteIndependentGraphRootDataExists H I p hY h hh hH e
        (lt_trans Nat.zero_lt_one hd1) hind hGauss c := by
  obtain ⟨p, hY, h, c, hh, e, hc0, hc, hdata⟩ :=
    original_fixed_vertex_map_constructs_finite_independent_cone_root_data H I hH hind hGauss hN hrank hd1 hvertex
  exact ⟨p, hY, h, c, hh, e, hc0, hc,
    actual_finite_independent_native_root_data_constructs_exact_graph_root_data H I p hY h hh hH e
      (lt_trans Nat.zero_lt_one hd1) hind hGauss c hc hc0 hdata⟩

end DimensionFourDependence
