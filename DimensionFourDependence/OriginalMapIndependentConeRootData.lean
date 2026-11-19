import DimensionFourDependence.ActualGaussIndependentConeRootData
import DimensionFourDependence.ActualFiniteNativeRootConstruction
import DimensionFourDependence.OriginalMapGaussRootForms
import DimensionFourDependence.BoundaryIndependentConeRootData
import DimensionFourDependence.BoundaryCanonicalIndependentRootData

/-! # The original fixed-vertex map constructs finite independent root data

The original valuation, algebraic residue field, actual boundary point
and finite parameter-coefficient field are retained together. Both old
root alternatives construct new independent forms on the same original
ruling, without changing the finite field or its parameter action.
-/

namespace DimensionFourDependence

open MvPolynomial Matrix AlgebraicGeometry

attribute [local instance] coefficientFieldScalarTower

universe u

set_option quotPrecheck false
set_option maxHeartbeats 6000000
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
local notation "ν" => actualClosedGaussFirstInvariantCovector H I p hY h hh
local notation "f₀" => closedGaussCoefficientParameterHom H I p hY h hh e
local notation "A₀" => closedGaussCoefficientGraphSlope H I p hY h hh e
local notation "n₀" => parametricRulingDenominator (f₀) (A₀) (coefficientCoordinate (K := K) (Y))

/-- The actual boundary and algebraic residue field, together with
the same finite original parameter field and independent native root
forms whose power form vanishes precisely on the fourth-axis ruling
direction. No original valuation or coefficient compatibility is lost. -/
noncomputable def ActualFiniteIndependentConeRootDataExists : Prop :=
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
        let g := IsScalarTower.toAlgHom K (L) κ
        ∃ E : IntermediateField (g.comp ((a).comp e.toAlgHom)).fieldRange κ,
          ∃ hfin : Module.Finite (g.comp ((a).comp e.toAlgHom)).fieldRange E,
          let : Module.Finite (g.comp ((a).comp e.toAlgHom)).fieldRange E := hfin
          let : Algebra C₀ E := parameterImageFiniteExtensionAlgebra (a) e g E
          let : Module.Finite C₀ E := parameterImageFiniteExtensionAlgebra_finite (a) e g E
          let : Algebra.IsAlgebraic C₀ E := inferInstance
          ActualChosenIndependentGaussRootDataForNumerator H I E hH e hd hind hGauss
            (closedGaussCanonicalRootNumerator H I p hY h hh e E)

/-- The original boundary construction retains its algebraic
residue extension and actual point while constructing independent
fixed-vertex root forms over the very same finite coefficient field. -/
theorem actual_boundary_constructs_finite_independent_fixed_vertex_root_data
    (hrank : polyRank (jac H) = 3) (hN : IsNilpotent (jac H)) (hd1 : 1 < d)
    (hvertex : rationalImageNormal H I.equation (Fin.last 3) = 0)
    (c : L) (hc : (c : S₀) = firstFiberInvariantInChart p (Y) hY h) (hc0 : c ≠ 0)
    (hdata : ActualGaussBoundaryRootFormsExist H I p hY h c hh e d) :
    ActualFiniteIndependentConeRootDataExists H I p hY h hh hH e hd hind hGauss := by
  obtain ⟨V, hV, hrest⟩ := hdata
  refine ⟨V, hV, ?_⟩
  let : Algebra (L) V := valuationConstantAlgebra V hV
  let : IsScalarTower (L) V S₀ := valuationConstantScalarTower V hV
  let κ := IsLocalRing.ResidueField V
  let : Algebra K κ := ((algebraMap (L) κ).comp (algebraMap K (L))).toAlgebra
  let : IsScalarTower K (L) κ := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  obtain ⟨i, scale, z, hz0, hz, hr0, hr1, hκalg, hres, hboundary, hv, hforms⟩ := hrest
  let : Algebra.IsAlgebraic (L) κ := hκalg
  let g := IsScalarTower.toAlgHom K (L) κ
  obtain ⟨E, hfin, n, m, s, rho, hn, hm, hs, _hrho, hny, hprod, hroot, _hsv, _hEuler, _hformula, hnumerator⟩ := hforms
  let E' : IntermediateField (g.comp ((a).comp e.toAlgHom)).fieldRange κ := E
  have hfin' : Module.Finite (g.comp ((a).comp e.toAlgHom)).fieldRange E' := hfin
  refine ⟨i, scale, z, hz0, hz, hr0, hr1, hκalg, hres, hboundary, hv, E', hfin', ?_⟩
  let : Module.Finite (g.comp ((a).comp e.toAlgHom)).fieldRange E' := hfin'
  let : Algebra C₀ E' := parameterImageFiniteExtensionAlgebra (a) e g E'
  let : Module.Finite C₀ E' := parameterImageFiniteExtensionAlgebra_finite (a) e g E'
  let : Algebra.IsAlgebraic C₀ E' := inferInstance
  have hcompat := parameterImageFiniteExtensionAlgebra_target_tower (a) e g E'
  have hnvalue : (∑ j, algebraMap E' κ (n j) * algebraMap (L) κ (coefficientCoordinate (K := K) (Y) j)) ≠ 0 := by
    rw [show (∑ j, algebraMap E' κ (n j) * algebraMap (L) κ (coefficientCoordinate (K := K) (Y) j)) =
      g (n₀) from hny]
    exact (map_ne_zero g).mpr (actual_closed_gauss_graph_denominator_ne_zero H I p hY h hh e hGauss hd hH)
  have hnum : ∀ j, n j = algebraMap C₀ E' (closedGaussRootNumeratorCoefficient H I p hY h hh e j) := by
    intro j
    change n j = algebraMap C₀ E' (e (rationalParameterDerivative K
      (rationalParameterDerivative K ((A₀) j))))
    rw [parameterImageFiniteExtensionAlgebra_parameter_value]
    exact hnumerator j
  exact specified_boundary_constructs_independent_root_data_for_original_canonical_numerator
    H hrank hN I p hY h hh E' hd1 hH hind hGauss hvertex e κ hcompat c hc hc0
      n m s rho hn hm hs hnvalue hprod hroot hnum

omit p hY h hh e hd in
/-- The original nonplanar fixed-vertex map constructs its own
chart, actual nonzero first invariant, valuation boundary, algebraic
residue extension and finite independent ruling root data. Neither
root alternatives, a cone formula nor independence is assumed. -/
theorem original_fixed_vertex_map_constructs_finite_independent_cone_root_data
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
      ActualFiniteIndependentConeRootDataExists H I p hY h hh hH e
        (lt_trans Nat.zero_lt_one hd1) hind hGauss := by
  have hd0 : 0 < d := lt_trans Nat.zero_lt_one hd1
  obtain ⟨W⟩ := exists_fiber_equation_witness_polynomial H hN hrank
  obtain ⟨h, c, q, k, hh, hc, hq, hk, hc0, _hEuler, _hcEuler, _hHess⟩ :=
    developable_fiber_witness_nonzero_weighted_invariants H hd0 hH hN hrank hind I
      (by rw [hGauss]) W
  obtain ⟨e⟩ := actual_closed_gauss_parameter_rational_function_field H I hGauss
  have hdata := actual_gauss_boundary_root_forms_exist H hrank I W.chart W.independent h c hh e
    hd0 hH hN hind hGauss hc0 q k hc hq hk
  exact ⟨W.chart, W.independent, h, c, hh, e, hc0, hc,
    actual_boundary_constructs_finite_independent_fixed_vertex_root_data H I W.chart W.independent h hh
      hH e hd0 hind hGauss hrank hN hd1 hvertex c hc hc0 hdata⟩

end DimensionFourDependence
