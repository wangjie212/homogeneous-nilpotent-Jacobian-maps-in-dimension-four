import DimensionFourDependence.ActualClosedGaussSimpleBoundaryChart
import DimensionFourDependence.OriginalMapGaussRootForms
import DimensionFourDependence.ActualSimpleRootInfinitySupport
import DimensionFourDependence.OriginalFiberInfinityChartDegree
import DimensionFourDependence.FullSourceDegree
import DimensionFourDependence.ActualNonlinearFiberDegree
import DimensionFourDependence.ActualDevelopableParabola
import DimensionFourDependence.ParabolaCoordinateAlgebra
import DimensionFourDependence.OriginalFiberRadialDegree
import DimensionFourDependence.OriginalClosureInfinitySupport

/-! # The original map constructs the finite simple-root local model

Retain the actual finite root construction's coefficient field and
root forms. Whenever those forms are independent on the actual ruling,
the same witnesses construct an invertible chart at an actual boundary
point of the original projected fiber and its full local length bound.
The same root witnesses also give a rational point containing the entire
actual extended full-fiber infinity support and bound the actual original
full-fiber Hilbert degree by two. If the actual fiber is nonlinear,
its degree is exactly two and the same original coordinates have a
nondegenerate quadratic parametrization and smooth polynomial coordinate
algebra over the actual coefficient field. Its radial projective-source
degree is also two, and the fixed infinity support point is an actual
point of the section. Independence remains the explicit Section 4.3
case distinction.
-/

namespace DimensionFourDependence

open MvPolynomial Matrix Module

attribute [local instance] coefficientFieldScalarTower MvPolynomial.gradedAlgebra

universe u

set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 100000
set_option quotPrecheck false

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
local notation "x₃" => fun i : Fin 3 => rationalCoordinate (K := K) (p i.castSucc)
local notation "f₀" => closedGaussCoefficientParameterHom H I p hY h hh e
local notation "A₀" => closedGaussCoefficientGraphSlope H I p hY h hh e
local notation "y₀" => coefficientCoordinate (K := K) (Y)
local notation "n₀" => parametricRulingDenominator (f₀) (A₀) (y₀)

/-- Actual finite root witnesses, their constructed local chart,
uniform rational infinity support, original degree bound and an exact
degree-two parabola parametrization for a nonlinear independent-root fiber. -/
noncomputable def ActualFiniteGaussSimpleRootChartDataExist (d : ℕ) : Prop :=
  ∃ (F : Type u) (hF : Field F),
    letI : Field F := hF
    ∃ aLF : Algebra (L) F,
      letI : Algebra (L) F := aLF
      ∃ aKF : Algebra K F,
        letI : Algebra K F := aKF
        ∃ htower : IsScalarTower K (L) F,
          letI : IsScalarTower K (L) F := htower
          ∃ hAlg : Algebra.IsAlgebraic (L) F,
            letI : Algebra.IsAlgebraic (L) F := hAlg
            let g := IsScalarTower.toAlgHom K (L) F
            let f := g.comp (f₀)
            let y := fun i => g ((y₀) i)
            ∃ C : IntermediateField f.fieldRange F, Module.Finite f.fieldRange C ∧
              ∃ (m s : Fin 3 → C) (rho : F), rho ≠ 0 ∧
                g (n₀) * g c = ((fun i => (m i : F)) ⬝ᵥ y) * rho ∧
                rho ^ d = (fun i => (s i : F)) ⬝ᵥ y ∧
                (LinearIndependent C ![rulingFormRestriction (finiteParameterGraphRuling f C (A₀)) m,
                  rulingFormRestriction (finiteParameterGraphRuling f C (A₀)) s] →
                  (∀ eCurve : ℕ, HasCurveHilbertDegree
                    (projectiveConeIdeal («L» := L) (rationalCoordinate (K := K) (n := 4))) eCurve →
                      eCurve ≤ 2 ∧
                        (¬ LiesInAffineLine (E := L) (rationalCoordinate (K := K) (n := 4)) →
                          eCurve = 2 ∧ LiesInAffineParabola («L» := L)
                            (rationalCoordinate (K := K) (n := 4)) ∧
                          Nonempty (Polynomial (L) ≃ₐ[L] (MvPolynomial (Fin 4) (L) ⧸
                            fiberVanishingIdeal («L» := L) (rationalCoordinate (K := K) (n := 4)))) ∧
                          Algebra.Smooth (L) (MvPolynomial (Fin 4) (L) ⧸
                            fiberVanishingIdeal («L» := L) (rationalCoordinate (K := K) (n := 4))) ∧
                          HasCurveHilbertDegree (projectiveFieldPointIdeal (E := L)
                            (rationalCoordinate (K := K) (n := 4))).toIdeal 2)) ∧
                  (∃ w a b : Fin 3 → C,
                    (rulingBoundaryCoordinateMatrix w a b).det ≠ 0 ∧
                    (rulingBoundaryCoordinateMatrix (fun i => (w i : F))
                      (fun i => (a i : F)) (fun i => (b i : F))).det ≠ 0 ∧
                    ∃ hb : (fun i => (b i : F)) ≠ 0,
                      projectiveFieldPoint (E := L) (fun j : Option (Fin 3) => j.elim 0 (fun i => (b i : F)))
                        (infinity_direction_projective_coordinates_ne_zero _ hb) ∈
                          projectiveClosureSet («L» := L) (x₃) ∧
                      HasOriginLocalLengthAtMostTwo (extendedProjectiveInfinityChartIdeal (E := L) (x₃)
                        (fun i => (b i : F)) (fun i => (w i : F)) (fun i => (a i : F)))) ∧
                  ∃ (B : Fin 4 → F) (hB : B ≠ 0),
                    let sB := projectiveFieldPoint (E := F) (fun j : Option (Fin 4) => j.elim 0 B)
                      (by
                        intro hzero
                        apply hB
                        funext i
                        exact congrFun hzero (some i))
                    (Ideal.map (MvPolynomial.map (algebraMap (L) F))
                        (projectiveConeIdeal («L» := L) (rationalCoordinate (K := K) (n := 4))) ⊔
                      Ideal.span ({X none} : Set (MvPolynomial (Option (Fin 4)) F)) ≤
                        sB.asHomogeneousIdeal.toIdeal) ∧
                    ∀ z : ProjectiveSpectrum (homogeneousSubmodule (Option (Fin 4)) F),
                      Ideal.map (MvPolynomial.map (algebraMap (L) F))
                          (projectiveConeIdeal («L» := L) (rationalCoordinate (K := K) (n := 4))) ⊔
                        Ideal.span ({X none} : Set (MvPolynomial (Option (Fin 4)) F)) ≤
                          z.asHomogeneousIdeal.toIdeal →
                      z = sB)

/-- The original finite valuation/root construction supplies the same
root witnesses, actual local model, uniform full infinity support and
the actual original full-fiber degree bound, exact for a nonlinear fiber. -/
theorem actual_gauss_boundary_root_forms_construct_simple_chart_data
    (hrank : polyRank (jac H) = 3)
    {d : ℕ} (hd : 1 < d) (hH : IsHomogMap H d) (hN : IsNilpotent (jac H))
    (hind : ¬ ComponentsDependent H) (hGauss : gaussImageDimension H I = 1)
    (hc0 : c ≠ 0)
    (q k : L) (hc : (c : S₀) = firstFiberInvariantInChart p (Y) hY h)
    (hq : (q : S₀) = secondFiberInvariant p (Y) hY h c)
    (hk : (k : S₀) = thirdFiberInvariant p (Y) hY h c q)
    (hdata : ActualGaussBoundaryRootFormsExist H I p hY h c hh e d) :
    ActualFiniteGaussSimpleRootChartDataExist H I p hY h c hh e d := by
  obtain ⟨V, hV, hrest⟩ := hdata
  let : Algebra (L) V := valuationConstantAlgebra V hV
  let : IsScalarTower (L) V S₀ := valuationConstantScalarTower V hV
  let F := IsLocalRing.ResidueField V
  let : Algebra K F := ((algebraMap (L) F).comp (algebraMap K (L))).toAlgebra
  let : IsScalarTower K (L) F := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  obtain ⟨_i, _scale, z, _hz0, _hz, hr0, _hr1, hAlg, hres, hboundary, hv0, hforms⟩ := hrest
  let : Algebra.IsAlgebraic (L) F := hAlg
  let g := IsScalarTower.toAlgHom K (L) F
  let f := g.comp (f₀)
  let y := fun i => g ((y₀) i)
  obtain ⟨C, hfin, n, m, s, rho, _hn, _hm, _hs, hrho, hny, hprod, hroot, hsv, _hD, _hrat, _hnvalue⟩ := hforms
  let : Module.Finite f.fieldRange C := hfin
  have hprod' : g (n₀) * g c = ((fun i => (m i : F)) ⬝ᵥ y) * rho := by
    rw [← hny]
    exact hprod
  refine ⟨F, inferInstance, inferInstance, inferInstance, inferInstance, hAlg,
    C, hfin, m, s, rho, hrho, hprod', hroot, ?_⟩
  intro hpair
  have hlocal := actual_closed_gauss_independent_root_boundary_chart_local_bound H I p hY h hh e F
    hd hH hGauss c q k hq hk (fun j => IsLocalRing.residue V (z j)) hres hboundary hr0 hv0
    C m s hpair rho hrho hprod' hroot hsv
  have hfirst : (fun i => f (rationalParameterDerivative K ((A₀) i))) ≠ 0 := by
    intro hzero
    apply actual_closed_gauss_graph_gradient_derivative_ne_zero H I p hY h hh e hGauss
    funext i
    apply g.injective
    change g ((f₀) (rationalParameterDerivative K ((A₀) i))) = g 0
    simpa only [f, map_zero, AlgHom.comp_apply, Pi.zero_apply] using congrFun hzero i
  obtain ⟨b, a, _hLI, hb, ha, hmb, hsb, hma, hsa, _hspan⟩ :=
    two_dimensional_ruling_coordinate_basis (finiteParameterGraphRuling f C (A₀))
      (finiteParameterGraphRuling_finrank f C (A₀) hfirst) m s hpair
  obtain ⟨hbF, hsupport⟩ := actual_extended_full_fiber_simple_root_infinity_support_single_point
    H hrank I p hY h hh e F hd hH hN hind hGauss c q k hc hq hk
    C m s b a hpair hb ha hmb hsb hma hsa rho hrho hprod' hroot
  have hfixedmem := original_boundary_constructs_fixed_support_membership (E := L)
    (rationalCoordinate (K := K) (n := 4)) (fun j => IsLocalRing.residue V (z j))
    hres hboundary hr0 _ hsupport
  refine ⟨?_, hlocal, graphBoundaryDirection p (fun i => f ((A₀) i)) (fun i => (b i : F)),
    graphBoundaryDirection_ne_zero p (fun i => f ((A₀) i)) (fun i => (b i : F)) hbF, hfixedmem, hsupport⟩
  intro eCurve heCurve
  obtain ⟨w', a', b', _hdetC, hdetF, _hb', _hpoint', hlocal'⟩ := hlocal
  have hupper := actual_full_fiber_degree_le_two_of_single_support_chart p (Y) hY h c hc F heCurve
    _ hsupport (fun i => (b' i : F)) (fun i => (w' i : F)) (fun i => (a' i : F)) hdetF hlocal'
  refine ⟨hupper, ?_⟩
  intro hline
  have heq := actual_nonlinear_full_fiber_hilbert_degree_eq_two H hN hrank p hY heCurve hline hupper
  have hpara := actual_developable_full_fiber_degree_bound_constructs_parabola H I p hY h hh e hGauss
    (by omega) hH c q hc0 hc hq heCurve hupper hline
  have hradial := (actual_first_invariant_radial_curve_degree p (Y) hY h c hc hc0 eCurve).mp heCurve
  rw [heq] at hradial
  exact ⟨heq, hpara, parabola_coordinate_quotient_polynomial_equiv _ hpara,
    parabola_coordinate_quotient_smooth _ hpara, hradial⟩

end DimensionFourDependence

namespace DimensionFourDependence

open MvPolynomial

universe u

variable {K : Type u} [Field K] [CharZero K]

/-- The original homogeneous nilpotent nonplanar rank-three map of
Gauss dimension one constructs its finite root data and, in the
independent-root case, the full actual infinity-chart local model,
a rational point containing the entire actual full infinity support,
and the bound two on the original full-fiber Hilbert degree. A nonlinear
actual fiber has exact affine and radial projective degree two, an
original-coordinate quadratic parabola parametrization and a smooth
polynomial coordinate quotient. The fixed infinity point belongs to
the actual section and is its unique support. A positive
integral Hilbert degree is constructed for this same original coefficient field.
No finite extension, root, boundary point, chart or local model is supplied. -/
theorem original_nonplanar_developable_map_constructs_simple_root_local_chart_data
    (H : Fin 4 → MvPolynomial (Fin 4) K) {d : ℕ} (hd : 1 < d) (hH : IsHomogMap H d)
    (hN : IsNilpotent (jac H)) (hrank : polyRank (jac H) = 3)
    (hind : ¬ ComponentsDependent H) (I : ImageRelationWitness H)
    (hGauss : gaussImageDimension H I = 1) :
    ∃ (p : Equiv.Perm (Fin 4))
      (hY : AlgebraicIndependent K (fun i : Fin 3 => algebraMap (MvPolynomial (Fin 4) K)
        (FractionRing (MvPolynomial (Fin 4) K)) (H (p i.castSucc))))
      (h c : coefficientField (K := K) (fun i : Fin 3 => algebraMap (MvPolynomial (Fin 4) K)
        (FractionRing (MvPolynomial (Fin 4) K)) (H (p i.castSucc))))
      (hh : (h : FractionRing (MvPolynomial (Fin 4) K)) = algebraMap (MvPolynomial (Fin 4) K)
        (FractionRing (MvPolynomial (Fin 4) K)) (H (p 3)))
      (e : RatFunc K ≃ₐ[K] closedGaussParameterField H I),
      c ≠ 0 ∧
        (∃ eCurve : ℕ, HasCurveHilbertDegree
          (projectiveConeIdeal (L := coefficientField (K := K) (fun i : Fin 3 =>
            algebraMap (MvPolynomial (Fin 4) K) (FractionRing (MvPolynomial (Fin 4) K))
              (H (p i.castSucc)))) (rationalCoordinate (K := K) (n := 4))) eCurve) ∧
        ActualFiniteGaussSimpleRootChartDataExist H I p hY h c hh e d := by
  have hd0 : 0 < d := by omega
  obtain ⟨P⟩ := exists_projective_fiber_equation_witness_polynomial H hN hrank
  let W := P.affine.toFiberEquationWitness
  have hNQ : IsNilpotent (rationalJacobian (fun i => algebraMap (MvPolynomial (Fin 4) K)
      (FractionRing (MvPolynomial (Fin 4) K)) (H i))) := by
    rw [rationalJacobian_polynomial]
    exact hN.map (algebraMap (MvPolynomial (Fin 4) K)
      (FractionRing (MvPolynomial (Fin 4) K))).mapMatrix
  have hrankQ : (rationalJacobian (fun i => algebraMap (MvPolynomial (Fin 4) K)
      (FractionRing (MvPolynomial (Fin 4) K)) (H i))).rank = 3 := by
    rw [rationalJacobian_polynomial]
    exact hrank
  obtain ⟨eCurve, _he6, heCurve⟩ := fiber_witness_full_source_degree _ hNQ hrankQ P
  obtain ⟨h, c, q, k, hh, hc, hq, hk, hc0, _hEuler, _hcEuler, _hHess⟩ :=
    developable_fiber_witness_nonzero_weighted_invariants H hd0 hH hN hrank hind I
      (by rw [hGauss]) W
  obtain ⟨e⟩ := actual_closed_gauss_parameter_rational_function_field H I hGauss
  have hdata := actual_gauss_boundary_root_forms_exist H hrank I W.chart W.independent h c hh e
    hd0 hH hN hind hGauss hc0 q k hc hq hk
  exact ⟨W.chart, W.independent, h, c, hh, e, hc0, ⟨eCurve, heCurve⟩,
    actual_gauss_boundary_root_forms_construct_simple_chart_data H I W.chart W.independent h c hh e
      hrank hd hH hN hind hGauss hc0 q k hc hq hk hdata⟩

end DimensionFourDependence
