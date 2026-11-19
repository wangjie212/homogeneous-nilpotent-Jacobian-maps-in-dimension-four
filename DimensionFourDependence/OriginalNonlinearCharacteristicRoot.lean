import DimensionFourDependence.IndependentNormalCharacteristicRoot
import DimensionFourDependence.NonlinearNormalPencilBase
import DimensionFourDependence.OriginalMapRootAlternatives

/-! # The original nonlinear map constructs its characteristic root factorization -/

namespace DimensionFourDependence

open MvPolynomial

universe u

set_option quotPrecheck false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 100000
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

variable {K : Type u} [kField : Field K] [kCharZero : CharZero K]
    (H : Fin 4 → MvPolynomial (Fin 4) K) (I : ImageRelationWitness H)
    {d : ℕ} (hH : IsHomogMap H d)
    (e : RatFunc K ≃ₐ[K] closedGaussParameterField H I)
    (hd : 0 < d) (hind : ¬ComponentsDependent H) (hGauss : gaussImageDimension H I = 1)

/-- A finite extension of the specified original closed Gauss field
carries the actual characteristic-case native root data. -/
noncomputable def ActualFiniteCharacteristicGaussRootDataExists : Prop :=
  ∃ (F : Type u) (hF : Field F),
    letI : Field F := hF
    ∃ aCF : Algebra (closedGaussParameterField H I) F,
      letI : Algebra (closedGaussParameterField H I) F := aCF
      ∃ hfin : Module.Finite (closedGaussParameterField H I) F,
        letI : Module.Finite (closedGaussParameterField H I) F := hfin
        letI : Algebra.IsAlgebraic (closedGaussParameterField H I) F := inferInstance
        ActualCharacteristicGaussRootData H I F hH e hd hind hGauss

omit e hd in
/-- From the actual original nonlinear component, construct the
finite coefficients, original rational Gauss parameter, nonzero native
root and characteristic factorization (4.6). Both other root cases
are excluded internally; no case, base geometry or factorization is supplied. -/
theorem original_nonlinear_gauss_curve_map_constructs_characteristic_root_factorization
    [IsAlgClosed K] (hd1 : 1 < d)
    (hN : IsNilpotent (jac H)) (hrank : polyRank (jac H) = 3)
    (E : Type u) [Field E] [Algebra (polynomialOutputField H) E] [Algebra K E]
    [IsScalarTower K (polynomialOutputField H) E] [IsAlgClosed E]
    [Algebra.IsAlgebraic (polynomialOutputField H) E]
    (P : Ideal (MvPolynomial (Fin 4) E)) [P.IsPrime]
    (hP : P ∈ (extendCoefficientIdeal E (fiberVanishingIdeal
      (L := polynomialOutputField H) (rationalCoordinate (K := K) (n := 4)))).minimalPrimes)
    (hline : ¬LiesInAffineLine (E := E) (primeQuotientCoordinate P)) :
    ∃ e : RatFunc K ≃ₐ[K] closedGaussParameterField H I,
      ActualFiniteCharacteristicGaussRootDataExists H I hH e (Nat.lt_trans Nat.zero_lt_one hd1) hind hGauss := by
  have hd0 : 0 < d := by omega
  have hNormal := nonlinear_geometric_component_original_normal_independent
    H hd1 hH hN hrank hind I hGauss E P hP hline
  obtain ⟨p, hY, h, hh, e, hdata⟩ :=
    original_nonplanar_developable_map_constructs_two_gauss_root_alternatives H hd0 hH hN hrank hind I hGauss
  let L := coefficientField (K := K) (fun i : Fin 3 => algebraMap (MvPolynomial (Fin 4) K)
    (FractionRing (MvPolynomial (Fin 4) K)) (H (p i.castSucc)))
  let a := actualClosedGaussCoefficientHom H I p hY h hh
  obtain ⟨V, hV, hrest⟩ := hdata
  let aLV : Algebra L V := valuationConstantAlgebra V hV
  let tLVS : IsScalarTower L V (FractionRing (MvPolynomial (Fin 4) K)) := valuationConstantScalarTower V hV
  let κ := IsLocalRing.ResidueField V
  let aKκ : Algebra K κ := ((algebraMap L κ).comp (algebraMap K L)).toAlgebra
  let tKLκ : IsScalarTower K L κ := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  let g := IsScalarTower.toAlgHom K L κ
  obtain ⟨F, hfin, hforms⟩ := hrest
  let fieldF : Field F := inferInstance
  let finImageF : Module.Finite (g.comp (a.comp e.toAlgHom)).fieldRange F := hfin
  let aCF : Algebra (closedGaussParameterField H I) F := parameterImageFiniteExtensionAlgebra a e g F
  let finCF : Module.Finite (closedGaussParameterField H I) F := parameterImageFiniteExtensionAlgebra_finite a e g F
  let algCF : Algebra.IsAlgebraic (closedGaussParameterField H I) F := inferInstance
  have hchar := @independent_normal_root_forms_construct_characteristic_factorization
    K kField kCharZero H I F fieldF aCF algCF d hH e hd0 hind hGauss hNormal hforms
  exact ⟨e, F, fieldF, aCF, finCF, hchar⟩

end DimensionFourDependence
