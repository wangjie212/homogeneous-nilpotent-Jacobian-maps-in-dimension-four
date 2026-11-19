import DimensionFourDependence.ActualFiniteNativeRootConstruction
import DimensionFourDependence.ActualChosenRootAlternatives
import DimensionFourDependence.NativeProportionalPowerFactorization

/-! # The actual finite boundary construction supplies the two remaining chosen-ruling cases

Keep the finite coefficient field and its actual original closed Gauss
action from the boundary construction. The constructed root is converted
to the chosen native tangent-plane formula, its binary relation is
derived, and the independent binary branch is excluded.
-/

namespace DimensionFourDependence

open MvPolynomial Matrix AlgebraicGeometry

attribute [local instance] coefficientFieldScalarTower

universe u

set_option quotPrecheck false
set_option maxHeartbeats 800000
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
    (hd : 0 < d) (hind : ¬ ComponentsDependent H) (hGauss : gaussImageDimension H I = 1)

local notation "C₀" => closedGaussParameterField H I
local notation "S₀" => FractionRing (MvPolynomial (Fin 4) K)
local notation "Y" => fun i : Fin 3 => algebraMap (MvPolynomial (Fin 4) K) S₀ (H (p i.castSucc))
local notation "L" => coefficientField (K := K) (Y)
local notation "a" => actualClosedGaussCoefficientHom H I p hY h hh

/-- The original actual finite boundary coefficient field, with
its specified closed Gauss action, supplies the actual chosen-plane
root formula and the paper's two remaining ruling-form alternatives,
including their constructed actual native algebraic normal forms. -/
noncomputable def ActualFiniteChosenGaussRootAlternativesExist : Prop :=
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
      ActualChosenGaussRootNormalForms H I E hH e hd hind hGauss

/-- The actual constructed native root forms give the chosen-plane
root data and the two remaining proportional alternatives. No scalar
normalization, binary relation or excluded-branch hypothesis is supplied. -/
theorem actual_finite_native_root_forms_construct_two_chosen_ruling_alternatives
    (hdata : ActualFiniteNativeGaussRootFormsExist H I p hY h hh hH e) :
    ActualFiniteChosenGaussRootAlternativesExist H I p hY h hh hH e hd hind hGauss := by
  obtain ⟨V, hV, hrest⟩ := hdata
  refine ⟨V, hV, ?_⟩
  let : Algebra (L) V := valuationConstantAlgebra V hV
  let : IsScalarTower (L) V S₀ := valuationConstantScalarTower V hV
  let κ := IsLocalRing.ResidueField V
  let : Algebra K κ := ((algebraMap (L) κ).comp (algebraMap K (L))).toAlgebra
  let : IsScalarTower K (L) κ := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  let g := IsScalarTower.toAlgHom K (L) κ
  obtain ⟨E, hfin, hforms⟩ := hrest
  refine ⟨E, hfin, ?_⟩
  let : Module.Finite (g.comp ((a).comp e.toAlgHom)).fieldRange E := hfin
  let : Algebra C₀ E := parameterImageFiniteExtensionAlgebra (a) e g E
  let : Module.Finite C₀ E := parameterImageFiniteExtensionAlgebra_finite (a) e g E
  let : Algebra.IsAlgebraic C₀ E := inferInstance
  obtain ⟨n, m, s, hn, hm, hs, hmvalue, hr, hroot, _hsection, hnumerator⟩ := hforms
  have hchosen : ActualChosenGaussRationalRootData H I E hH e hd hind hGauss := by
    exact selected_root_forms_construct_chosen_ruling_root_data H I E hH e hd hind hGauss p hY h hh
      n m s hn hm hs hmvalue hr hroot hnumerator
  have halt : ActualChosenGaussRationalRootAlternatives H I E hH e hd hind hGauss :=
    actual_chosen_root_data_construct_two_alternatives H I E hH e hd hind hGauss hchosen
  exact actual_chosen_root_alternatives_construct_native_normal_forms H I E hH e hd hind hGauss halt

end DimensionFourDependence
