import DimensionFourDependence.RealizedAffineConeRootCases
import DimensionFourDependence.OriginalFixedVertexAffineRootCases

/-! # The original finite boundary root cases keep the actual geometric realization

The finite boundary coefficient field has its specified closed Gauss
action. Extending the actual geometric closed-field realization to that
same field transports the constructed affine root alternatives, with no
supplied coefficient embedding, scalar root or cone presentation.
-/

namespace DimensionFourDependence

open MvPolynomial

attribute [local instance] coefficientFieldScalarTower

universe u

set_option quotPrecheck false
set_option maxHeartbeats 4000000
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
    {E G : Type u} [Field E] [Field G] [Algebra K E] [Algebra E G] [Algebra K G]
    [IsScalarTower K E G] [IsAlgClosed E]

local notation "C₀" => closedGaussParameterField H I
local notation "S₀" => FractionRing (MvPolynomial (Fin 4) K)
local notation "Y" => fun i : Fin 3 => algebraMap (MvPolynomial (Fin 4) K) S₀ (H (p i.castSucc))
local notation "L" => coefficientField (K := K) (Y)
local notation "a" => actualClosedGaussCoefficientHom H I p hY h hh

/-- The actual finite original root alternatives transfer to every
compatible actual geometric source realization. The extended coefficient
embedding, nonzero constant root and complete second-case cone formula
are all constructed internally. -/
theorem actual_finite_affine_root_cases_transfer_to_source_realization
    (hvertex : rationalImageNormal H I.equation (Fin.last 3) = 0)
    (hdata : ActualFiniteAffineFixedVertexRootAlternativesExist H I p hY h hh hH e hd hind hGauss)
    (f : S₀ →ₐ[K] G) (g : C₀ →ₐ[K] E)
    (hg : ∀ c : C₀, algebraMap E G (g c) = f (c : S₀))
    (z : Fin 4 → G) (hf : ∀ i, f (rationalCoordinate (K := K) i) = z i)
    (y : Fin 4 → E) (hout : ∀ i, aeval z (H i) = algebraMap E G (y i)) :
    RealizedAffineFixedVertexRootAlternatives H I e g z y d := by
  obtain ⟨V, hV, hrest⟩ := hdata
  let : Algebra (L) V := valuationConstantAlgebra V hV
  let : IsScalarTower (L) V S₀ := valuationConstantScalarTower V hV
  let κ := IsLocalRing.ResidueField V
  let : Algebra K κ := ((algebraMap (L) κ).comp (algebraMap K (L))).toAlgebra
  let : IsScalarTower K (L) κ := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  let g₀ := IsScalarTower.toAlgHom K (L) κ
  obtain ⟨F, hfin, hforms⟩ := hrest
  let : Module.Finite (g₀.comp ((a).comp e.toAlgHom)).fieldRange F := hfin
  let : Algebra C₀ F := parameterImageFiniteExtensionAlgebra (a) e g₀ F
  let : Module.Finite C₀ F := parameterImageFiniteExtensionAlgebra_finite (a) e g₀ F
  let : Algebra.IsAlgebraic C₀ F := inferInstance
  exact affine_fixed_vertex_root_alternatives_transfer_to_actual_source_realization
    H I F hH hd hind hGauss hvertex e f g hg z hf y hout hforms

end DimensionFourDependence
