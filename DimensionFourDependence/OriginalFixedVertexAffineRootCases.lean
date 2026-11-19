import DimensionFourDependence.AffineFixedVertexRootAlternatives
import DimensionFourDependence.OriginalMapRootAlternatives

/-! # The original fixed-vertex map constructs its actual affine root alternatives

The actual boundary construction supplies its own finite coefficient
field with its original closed Gauss action. The proved native root cases
transfer to the original affine source over this same field. Thus the
original map constructs either its exact scaled-plane root or the full
cone expression (4.7), including the nonzero fourth coefficient.
-/

namespace DimensionFourDependence

open MvPolynomial

attribute [local instance] coefficientFieldScalarTower

universe u

set_option quotPrecheck false
set_option maxHeartbeats 3000000
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

/-- The actual finite boundary coefficient field, with its original
closed Gauss action, supplies both remaining root cases on the original
affine source. Its second case includes the complete cone formula. -/
noncomputable def ActualFiniteAffineFixedVertexRootAlternativesExist : Prop :=
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
      ActualAffineFixedVertexRootAlternatives H I E hH hd hind hGauss

/-- The actual original finite root-case construction supplies the
same finite coefficients and both exact affine root alternatives. -/
theorem actual_finite_chosen_root_forms_construct_affine_fixed_vertex_alternatives
    (hvertex : rationalImageNormal H I.equation (Fin.last 3) = 0)
    (hdata : ActualFiniteChosenGaussRootAlternativesExist H I p hY h hh hH e hd hind hGauss) :
    ActualFiniteAffineFixedVertexRootAlternativesExist H I p hY h hh hH e hd hind hGauss := by
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
  exact actual_chosen_root_normal_forms_construct_affine_fixed_vertex_alternatives
    H I E hH e hd hind hGauss hvertex hforms

omit p hY h hh e in
/-- The original homogeneous nilpotent rank-three independent map
with Gauss dimension one and specified fourth-axis vertex constructs
its own finite coefficients, nonzero affine rational root, exact power
identity, and either the scaled-plane case or the complete cone formula
(4.7). No root cases, factorization or cone presentation are supplied. -/
theorem original_nonplanar_fixed_vertex_map_constructs_affine_root_alternatives
    (hN : IsNilpotent (jac H)) (hrank : polyRank (jac H) = 3)
    (hvertex : rationalImageNormal H I.equation (Fin.last 3) = 0) :
    ∃ (p : Equiv.Perm (Fin 4))
      (hY : AlgebraicIndependent K (fun i : Fin 3 => algebraMap (MvPolynomial (Fin 4) K)
        (FractionRing (MvPolynomial (Fin 4) K)) (H (p i.castSucc))))
      (h : coefficientField (K := K) (fun i : Fin 3 => algebraMap (MvPolynomial (Fin 4) K)
        (FractionRing (MvPolynomial (Fin 4) K)) (H (p i.castSucc))))
      (hh : (h : FractionRing (MvPolynomial (Fin 4) K)) = algebraMap (MvPolynomial (Fin 4) K)
        (FractionRing (MvPolynomial (Fin 4) K)) (H (p 3)))
      (e : RatFunc K ≃ₐ[K] closedGaussParameterField H I),
      ActualFiniteAffineFixedVertexRootAlternativesExist H I p hY h hh hH e hd hind hGauss := by
  obtain ⟨p, hY, h, hh, e, hdata⟩ :=
    original_nonplanar_developable_map_constructs_two_gauss_root_alternatives H hd hH hN hrank hind I hGauss
  exact ⟨p, hY, h, hh, e,
    actual_finite_chosen_root_forms_construct_affine_fixed_vertex_alternatives
      H I p hY h hh hH e hd hind hGauss hvertex hdata⟩

end DimensionFourDependence
