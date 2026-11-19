import DimensionFourDependence.ActualBoundaryNativeRoot
import DimensionFourDependence.ParameterImageFiniteExtension
import DimensionFourDependence.ExtendedHomogeneousRootExistence
import DimensionFourDependence.ActualNativeRootNonzero
import DimensionFourDependence.GaussRootNumeratorCoefficients

/-! # The actual finite boundary root constructs native finite-coefficient root forms

The finite boundary coefficient field receives its specified original
closed Gauss action. This proves every compatibility needed by the tensor
transfer and constructs the native rational root with its original forms.
-/

namespace DimensionFourDependence

open MvPolynomial Matrix AlgebraicGeometry

attribute [local instance] coefficientFieldScalarTower

universe u

set_option quotPrecheck false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 100000
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

variable {K : Type u} [Field K] [CharZero K]
    (H : Fin 4 → MvPolynomial (Fin 4) K) (I : ImageRelationWitness H)
    (p : Equiv.Perm (Fin 4))
    (hY : AlgebraicIndependent K (fun i : Fin 3 => algebraMap (MvPolynomial (Fin 4) K)
      (FractionRing (MvPolynomial (Fin 4) K)) (H (p i.castSucc))))
    (h : coefficientField (K := K) (fun i : Fin 3 => algebraMap (MvPolynomial (Fin 4) K)
      (FractionRing (MvPolynomial (Fin 4) K)) (H (p i.castSucc))))
    (hh : (h : FractionRing (MvPolynomial (Fin 4) K)) = algebraMap (MvPolynomial (Fin 4) K)
      (FractionRing (MvPolynomial (Fin 4) K)) (H (p 3)))
    {d : ℕ} (hH : IsHomogMap H d) (e : RatFunc K ≃ₐ[K] closedGaussParameterField H I)

local notation "C₀" => closedGaussParameterField H I
local notation "S₀" => FractionRing (MvPolynomial (Fin 4) K)
local notation "Y" => fun i : Fin 3 => algebraMap (MvPolynomial (Fin 4) K) S₀ (H (p i.castSucc))
local notation "L" => coefficientField (K := K) (Y)
local notation "a" => actualClosedGaussCoefficientHom H I p hY h hh
local notation "ν" => actualClosedGaussFirstInvariantCovector H I p hY h hh
local notation "f₀" => closedGaussCoefficientParameterHom H I p hY h hh e

/-- Actual finite closed-Gauss coefficients and original-coordinate
forms construct a rational root in the actual normalized pencil field.
The finite coefficient action is specified by the actual parameter image. -/
noncomputable def ActualFiniteNativeGaussRootFormsExist : Prop :=
  ∃ (V : ValuationSubring S₀) (hV : ∀ b : L, (b : S₀) ∈ V),
    letI : Algebra (L) V := valuationConstantAlgebra V hV
    letI : IsScalarTower (L) V S₀ := valuationConstantScalarTower V hV
    let κ := IsLocalRing.ResidueField V
    letI : Algebra K κ := ((algebraMap (L) κ).comp (algebraMap K (L))).toAlgebra
    letI : IsScalarTower K (L) κ := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
    let g := IsScalarTower.toAlgHom K (L) κ
    ∃ E : IntermediateField (g.comp ((a).comp e.toAlgHom)).fieldRange κ,
      ∃ hfin : Module.Finite (g.comp ((a).comp e.toAlgHom)).fieldRange E,
      letI : Module.Finite (g.comp ((a).comp e.toAlgHom)).fieldRange E := hfin
      letI : Algebra C₀ E := parameterImageFiniteExtensionAlgebra (a) e g E
      letI : Module.Finite C₀ E := parameterImageFiniteExtensionAlgebra_finite (a) e g E
      letI : Algebra.IsAlgebraic C₀ E := inferInstance
      let N := extendedClosedGaussNormalizationScheme H I E hH e
      letI : IsIntegral N := extendedClosedGaussNormalizationScheme_isIntegral H I E hH e
      letI : Algebra E N.functionField := extendedClosedGaussOwnFunctionFieldAlgebra H I E hH e
      let w := extendedClosedGaussNormalizationHyperplaneWeight H I E hH e
      let P := selectedOutputLinearPolynomial H I E p
      let Q := MvPolynomial.map (algebraMap C₀ E) (linearFormPolynomial (ν))
      ∃ n m s : Fin 3 → E, n ≠ 0 ∧ m ≠ 0 ∧ s ≠ 0 ∧
        aeval w (P m) ≠ 0 ∧
        aeval w (P n) * aeval w Q / aeval w (P m) ≠ 0 ∧
        (aeval w (P n) * aeval w Q / aeval w (P m)) ^ d = aeval w (P s) ∧
        ExtendedClosedGaussNonzeroRootSectionExists H I E hH e (P s)
          (selectedOutputLinearPolynomial_homogeneous H I E hH p s)
          (aeval w (P n) * aeval w Q / aeval w (P m)) ∧
        (∀ i, n i = algebraMap C₀ E (closedGaussRootNumeratorCoefficient H I p hY h hh e i))

/-- The already constructed actual boundary forms give native
finite-coefficient root forms. No native identity, coefficient action,
faithful realization or nonzero native denominator is assumed. -/
theorem actual_finite_boundary_root_forms_construct_native_root_forms
    (hd : 0 < d)
    (c : L) (hc : (c : S₀) = firstFiberInvariantInChart p (Y) hY h) (hc0 : c ≠ 0)
    (hdata : ActualGaussBoundaryRootFormsExist H I p hY h c hh e d)
    (hn₀ : parametricRulingDenominator (f₀) (closedGaussCoefficientGraphSlope H I p hY h hh e)
      (coefficientCoordinate (K := K) (Y)) ≠ 0) :
    ActualFiniteNativeGaussRootFormsExist H I p hY h hh hH e := by
  obtain ⟨V, hV, hrest⟩ := hdata
  refine ⟨V, hV, ?_⟩
  let : Algebra (L) V := valuationConstantAlgebra V hV
  let : IsScalarTower (L) V S₀ := valuationConstantScalarTower V hV
  let κ := IsLocalRing.ResidueField V
  let : Algebra K κ := ((algebraMap (L) κ).comp (algebraMap K (L))).toAlgebra
  let : IsScalarTower K (L) κ := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  obtain ⟨_i, _scale, _z, _hz0, _hz, _hr0, _hr1, hκalg, _hres, _hboundary, _hv, hforms⟩ := hrest
  let : Algebra.IsAlgebraic (L) κ := hκalg
  let g := IsScalarTower.toAlgHom K (L) κ
  obtain ⟨E, hfin, n, m, s, ρ, hn, hm, hs, _hρ, hny, hprod, hroot, _hsv, _hρD, _hformula, hnumerator⟩ := hforms
  let E' : IntermediateField (g.comp ((a).comp e.toAlgHom)).fieldRange κ := E
  have hfin' : Module.Finite (g.comp ((a).comp e.toAlgHom)).fieldRange E' := hfin
  refine ⟨E', hfin', ?_⟩
  let : Module.Finite (g.comp ((a).comp e.toAlgHom)).fieldRange E' := hfin'
  let : Algebra C₀ E' := parameterImageFiniteExtensionAlgebra (a) e g E'
  let : Module.Finite C₀ E' := parameterImageFiniteExtensionAlgebra_finite (a) e g E'
  let : Algebra.IsAlgebraic C₀ E' := inferInstance
  have hcompat := parameterImageFiniteExtensionAlgebra_target_tower (a) e g E'
  have hnvalue : (∑ i, algebraMap E' κ (n i) * algebraMap (L) κ (coefficientCoordinate (K := K) (Y) i)) ≠ 0 := by
    rw [show (∑ i, algebraMap E' κ (n i) * algebraMap (L) κ (coefficientCoordinate (K := K) (Y) i)) =
      g (parametricRulingDenominator (f₀) (closedGaussCoefficientGraphSlope H I p hY h hh e)
        (coefficientCoordinate (K := K) (Y))) from hny]
    exact (map_ne_zero g).mpr hn₀
  refine ⟨n, m, s, hn, hm, hs, ?_⟩
  let N := extendedClosedGaussNormalizationScheme H I E' hH e
  let : IsIntegral N := extendedClosedGaussNormalizationScheme_isIntegral H I E' hH e
  let : Algebra E' N.functionField := extendedClosedGaussOwnFunctionFieldAlgebra H I E' hH e
  let w := extendedClosedGaussNormalizationHyperplaneWeight H I E' hH e
  let P := selectedOutputLinearPolynomial H I E' p
  let Q := MvPolynomial.map (algebraMap C₀ E') (linearFormPolynomial (ν))
  have hnative : aeval w (P m) ≠ 0 ∧
      (aeval w (P n) * aeval w Q / aeval w (P m)) ^ d = aeval w (P s) := by
    exact actual_boundary_equation_4_4_constructs_native_rational_root H I p hY h hh E' hH e κ
      hcompat c hc hc0 n m s ρ hnvalue hprod hroot
  have hmnative := hnative.1
  have hrootnative := hnative.2
  have hrnative := actual_boundary_rational_root_native_formula_ne_zero H I p hY h hh E' hH e κ
    hcompat c hc hc0 n m hnvalue hmnative
  refine ⟨hmnative, hrnative, hrootnative, ?_⟩
  refine ⟨?_, ?_⟩
  · exact extendedClosedGauss_nonzero_homogeneous_root_constructs_section H I E' hH e
      (selectedOutputLinearPolynomial H I E' p s)
      (selectedOutputLinearPolynomial_homogeneous H I E' hH p s) _ hrnative hd hrootnative
  · intro i
    change n i = algebraMap C₀ E' (e (rationalParameterDerivative K
      (rationalParameterDerivative K (closedGaussCoefficientGraphSlope H I p hY h hh e i))))
    rw [parameterImageFiniteExtensionAlgebra_parameter_value]
    exact hnumerator i

end DimensionFourDependence
