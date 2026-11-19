import DimensionFourDependence.ExtendedRationalRootSections
import DimensionFourDependence.ExtendedHomogeneousSectionCoefficients
import DimensionFourDependence.ExtendedNativeSectionMultiplicity

/-! # Extended original rational roots retain source coefficients and bounded divisor multiplicities -/

namespace DimensionFourDependence

open MvPolynomial AlgebraicGeometry

universe u

set_option synthInstance.maxHeartbeats 100000
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

variable {K : Type u} [Field K] [CharZero K]
  (H : Fin 4 → MvPolynomial (Fin 4) K) (I : ImageRelationWitness H)
  (E : Type u) [Field E] [Algebra (closedGaussParameterField H I) E]
  [Algebra.IsAlgebraic (closedGaussParameterField H I) E]
  {d : ℕ} (hH : IsHomogMap H d)
  (e : RatFunc K ≃ₐ[K] closedGaussParameterField H I)

local notation "N" => extendedClosedGaussNormalizationScheme H I E hH e
local notation "M" => extendedClosedGaussNormalizationHyperplaneModuleSheaf H I E hH e
local notation "U" a:max => extendedClosedGaussNormalizationChartOpen H I E hH e (finSuccEquiv' a)
local notation "w" => extendedClosedGaussNormalizationHyperplaneWeight H I E hH e

local instance extendedRationalRootMultiplicityIntegral : IsIntegral N :=
  extendedClosedGaussNormalizationScheme_isIntegral H I E hH e
local instance extendedRationalRootMultiplicityNoetherian : IsNoetherian N :=
  extendedClosedGaussNormalizationScheme_isNoetherian H I E hH e
noncomputable local instance extendedRationalRootMultiplicityAlgebra : Algebra E (N).functionField :=
  extendedClosedGaussOwnFunctionFieldAlgebra H I E hH e

/-- The actual regular root coefficient satisfies its original
power equation in every actual original chart ring. -/
theorem extendedClosedGaussHomogeneousRationalRootSection_coefficient_power
    (P : MvPolynomial (Fin 4) E) {n : ℕ} (hP : P.IsHomogeneous n)
    (r : (N).functionField) (hn : 0 < n) (hroot : r ^ n = aeval w P) (a : Fin 4) :
    extendedClosedGaussHyperplaneGlobalCoefficient H I E hH e
        (extendedClosedGaussHomogeneousRationalRootSection H I E hH e P hP r hn hroot) a ^ n =
      extendedClosedGaussChartPolynomialCoefficient H I E hH e P a := by
  let root := extendedClosedGaussHomogeneousRationalRootSection H I E hH e P hP r hn hroot
  have hp := rationalFrameGlobalCoefficient_power N (fun a : Fin 4 => U a) w
    (extendedClosedGaussNormalizationChartOpen_iSup H I E hH e)
    (extendedClosedGaussNormalizationHyperplaneWeight_ne_zero H I E hH e) root n a
  have hs := extendedClosedGaussHomogeneousRationalRootSection_power H I E hH e P hP r hn hroot
  have hc := congrArg (fun t : Γ(extendedClosedGaussHyperplanePowerModuleSheaf H I E hH e n, ⊤) =>
    extendedClosedGaussHyperplanePowerSectionCoefficient H I E hH e t a) hs
  exact hp.symm.trans (hc.trans
    (extendedClosedGaussHomogeneousPolynomialSection_coefficient H I E hH e P hP a))

/-- The rational root of an original ruling-linear combination of
the homogeneous map components is an actual regular global section. -/
noncomputable def extendedClosedGaussOutputLinearRootSection
    (c : Fin 4 → E) (r : (N).functionField) (hd : 0 < d)
    (hroot : r ^ d = aeval w (extendedClosedGaussOutputLinearPolynomial H I E c)) : Γ(M, ⊤) :=
  extendedClosedGaussHomogeneousRationalRootSection H I E hH e
    (extendedClosedGaussOutputLinearPolynomial H I E c)
    (extendedClosedGaussOutputLinearPolynomial_homogeneous H I E hH c) r hd hroot

/-- Normality extends the ruling's rational root without changing
its original rational value. -/
theorem extendedClosedGaussOutputLinearRootSection_value
    (c : Fin 4 → E) (r : (N).functionField) (hd : 0 < d)
    (hroot : r ^ d = aeval w (extendedClosedGaussOutputLinearPolynomial H I E c)) :
    extendedClosedGaussHyperplaneGlobalValue H I E hH e
      (extendedClosedGaussOutputLinearRootSection H I E hH e c r hd hroot) = r :=
  extendedClosedGaussHomogeneousRationalRootSection_value H I E hH e _ _ r hd hroot

/-- The actual power of the extended ruling root equals the actual
regular original output-linear global section. -/
theorem extendedClosedGaussOutputLinearRootSection_power
    (c : Fin 4 → E) (r : (N).functionField) (hd : 0 < d)
    (hroot : r ^ d = aeval w (extendedClosedGaussOutputLinearPolynomial H I E c)) :
    extendedClosedGaussHyperplaneSectionPower H I E hH e
        (extendedClosedGaussOutputLinearRootSection H I E hH e c r hd hroot) d =
      extendedClosedGaussOutputLinearSection H I E hH e c :=
  extendedClosedGaussHomogeneousRationalRootSection_power H I E hH e _ _ r hd hroot

variable (hGauss : gaussImageDimension H I = 1)
  (p q : MvPolynomial (Fin 4) K) {D : ℕ}
  (hq0 : q ≠ 0) (hrel : IsRelPrime p q) (hpH : p.IsHomogeneous D) (hqH : q.IsHomogeneous D)
  (ht : closedGaussParameterSourceHom H I e RatFunc.X =
    algebraMap _ (FractionRing (MvPolynomial (Fin 4) K)) p /
      algebraMap _ (FractionRing (MvPolynomial (Fin 4) K)) q)

include hGauss hq0 hrel hpH hqH ht in
/-- At every intrinsic normalization divisor, a nonzero original
rational section with actual regular positive power has an actual regular
original frame and integer multiplicity between zero and the pencil degree. -/
theorem actual_pencil_rational_root_divisor_multiplicity_bound
    (r : (N).functionField) (hr : r ≠ 0) {n : ℕ} (hn : 0 < n)
    (s : Γ(extendedClosedGaussHyperplanePowerModuleSheaf H I E hH e n, ⊤))
    (hs : rationalFrameGlobalSectionValue N (fun a : Fin 4 => U a) (fun a => w a ^ n) s = r ^ n)
    (z : N) (hcodim : Order.coheight z = 1) :
    ∃ a : Fin 4, z ∈ U a ∧
      0 ≤ (N).ord (r / w a) z ∧ (N).ord (r / w a) z ≤ (D : ℤ) := by
  let root := extendedClosedGaussHyperplaneRationalRootSection H I E hH e r hn s hs
  have hne := extendedClosedGaussHyperplaneRationalRootSection_ne_zero H I E hH e r hr hn s hs
  obtain ⟨a, hz, hb⟩ := actual_native_pencil_global_section_all_divisors_multiplicity_bound H I E hH e
    hGauss p q hq0 hrel hpH hqH ht root hne z hcodim
  let : Nonempty (U a) := ⟨⟨z, hz⟩⟩
  have hv : algebraMap ((N).presheaf.stalk z) (N).functionField
      ((N).presheaf.germ (U a) z hz (extendedClosedGaussHyperplaneGlobalCoefficient H I E hH e root a)) =
      r / w a :=
    (Scheme.algebraMap_germ_eq_germToFunctionField N hz _).trans
      (extendedClosedGaussHyperplaneRationalRootSection_coefficient H I E hH e r hn s hs a)
  refine ⟨a, hz, ?_⟩
  dsimp only at hb
  rwa [hv] at hb

include hGauss hq0 hrel hpH hqH ht in
/-- The paper's rational root of a ruling-linear output form has
pencil-degree-bounded actual divisor multiplicity; normality and the
actual regular source-form section supply the extension and all coefficients. -/
theorem actual_pencil_output_linear_root_divisor_multiplicity_bound
    (c : Fin 4 → E) (r : (N).functionField) (hr : r ≠ 0) (hd : 0 < d)
    (hroot : r ^ d = aeval w (extendedClosedGaussOutputLinearPolynomial H I E c))
    (z : N) (hcodim : Order.coheight z = 1) :
    ∃ a : Fin 4, z ∈ U a ∧
      0 ≤ (N).ord (r / w a) z ∧ (N).ord (r / w a) z ≤ (D : ℤ) :=
  actual_pencil_rational_root_divisor_multiplicity_bound H I E hH e hGauss
    p q hq0 hrel hpH hqH ht r hr hd (extendedClosedGaussOutputLinearSection H I E hH e c)
    ((extendedClosedGaussHomogeneousPolynomialSection_value H I E hH e
      (extendedClosedGaussOutputLinearPolynomial H I E c)
      (extendedClosedGaussOutputLinearPolynomial_homogeneous H I E hH c)).trans hroot.symm) z hcodim

end DimensionFourDependence
