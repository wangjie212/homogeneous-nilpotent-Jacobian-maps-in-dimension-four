import DimensionFourDependence.ActualGaussRootFullCone
import DimensionFourDependence.OriginalMapRootAlternatives

/-! # The original fixed-vertex map constructs its own full affine cone presentation -/

namespace DimensionFourDependence

open MvPolynomial
open scoped TensorProduct

attribute [local instance] coefficientFieldScalarTower Algebra.TensorProduct.rightAlgebra

universe u

set_option quotPrecheck false
set_option maxHeartbeats 3000000
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

local notation "C₀" => closedGaussParameterField H I
local notation "S₀" => FractionRing (MvPolynomial (Fin 4) K)
local notation "Y" => (fun i : Fin 3 => algebraMap (MvPolynomial (Fin 4) K) S₀ (H (p i.castSucc)))
local notation "L" => coefficientField (K := K) (Y)
local notation "a" => actualClosedGaussCoefficientHom H I p hY h hh

/-- The actual finite boundary coefficient field, with its original
closed Gauss action, supplies a nonzero root and the complete affine
cone formula (4.7), including its nonzero fourth coefficient. -/
noncomputable def ActualFiniteAffineFullConeExists : Prop :=
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
      letI : IsDomain (S₀ ⊗[C₀] E) :=
        (actual_closed_gauss_cover_algebraic_base_change_isField H I E).isDomain
      ∃ r : FractionRing (S₀ ⊗[C₀] E), r ≠ 0 ∧
        AffineSourceFixedVertexConeRootForm H I E hH hd hind hGauss r

/-- The original finite root normal forms supply the full cone
presentation over the same specified finite coefficient field. -/
theorem actual_finite_chosen_root_forms_construct_full_affine_cone
    (hN : IsNilpotent (jac H)) (hrank : polyRank (jac H) = 3) (hd1 : 1 < d)
    (hvertex : rationalImageNormal H I.equation (Fin.last 3) = 0)
    (hdata : ActualFiniteChosenGaussRootAlternativesExist H I p hY h hh hH e hd hind hGauss) :
    ActualFiniteAffineFullConeExists H I p hY h hh hH e hd hind hGauss := by
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
  exact actual_chosen_gauss_root_normal_forms_construct_full_affine_cone
    H hrank hN I E hd1 hH hind hGauss hvertex e hforms

omit p hY h hh e hd in
/-- The original homogeneous nilpotent rank-three independent map
with Gauss dimension one and specified fourth-axis vertex constructs
its own finite coefficients and complete affine cone formula (4.7).
No root alternatives, boundary, factorization or cone presentation
are supplied as additional hypotheses. -/
theorem original_nonplanar_fixed_vertex_map_constructs_full_affine_cone
    (hN : IsNilpotent (jac H)) (hrank : polyRank (jac H) = 3) (hd1 : 1 < d)
    (hvertex : rationalImageNormal H I.equation (Fin.last 3) = 0) :
    ∃ (p : Equiv.Perm (Fin 4))
      (hY : AlgebraicIndependent K (fun i : Fin 3 => algebraMap (MvPolynomial (Fin 4) K)
        (FractionRing (MvPolynomial (Fin 4) K)) (H (p i.castSucc))))
      (h : coefficientField (K := K) (fun i : Fin 3 => algebraMap (MvPolynomial (Fin 4) K)
        (FractionRing (MvPolynomial (Fin 4) K)) (H (p i.castSucc))))
      (hh : (h : FractionRing (MvPolynomial (Fin 4) K)) = algebraMap (MvPolynomial (Fin 4) K)
        (FractionRing (MvPolynomial (Fin 4) K)) (H (p 3)))
      (e : RatFunc K ≃ₐ[K] closedGaussParameterField H I),
      ActualFiniteAffineFullConeExists H I p hY h hh hH e (lt_trans Nat.zero_lt_one hd1) hind hGauss := by
  obtain ⟨p, hY, h, hh, e, hdata⟩ :=
    original_nonplanar_developable_map_constructs_two_gauss_root_alternatives
      H (lt_trans Nat.zero_lt_one hd1) hH hN hrank hind I hGauss
  exact ⟨p, hY, h, hh, e,
    actual_finite_chosen_root_forms_construct_full_affine_cone H I p hY h hh hH e
      (lt_trans Nat.zero_lt_one hd1) hind hGauss hN hrank hd1 hvertex hdata⟩

end DimensionFourDependence
