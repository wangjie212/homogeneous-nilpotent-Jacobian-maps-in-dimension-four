import DimensionFourDependence.RealizedAffineFullCone
import DimensionFourDependence.OriginalMapFullAffineCone

/-! # The constructed finite cone form retains the actual geometric realization -/

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
    {d : ℕ} (hH : IsHomogMap H d) (e₀ : RatFunc K ≃ₐ[K] closedGaussParameterField H I)
    (hd : 0 < d) (hind : ¬ComponentsDependent H) (hGauss : gaussImageDimension H I = 1)
    {E G : Type u} [Field E] [Field G] [Algebra K E] [Algebra E G] [Algebra K G]
    [IsScalarTower K E G] [IsAlgClosed E]

local notation "C₀" => closedGaussParameterField H I
local notation "S₀" => FractionRing (MvPolynomial (Fin 4) K)
local notation "Y" => (fun i : Fin 3 => algebraMap (MvPolynomial (Fin 4) K) S₀ (H (p i.castSucc)))
local notation "L" => coefficientField (K := K) (Y)
local notation "a" => actualClosedGaussCoefficientHom H I p hY h hh

/-- The same finite coefficient field constructed from the original
boundary supplies the full cone presentation in any compatible actual
source realization, expressed in any specified closed Gauss parameter.
No coefficient extension, scalar root or cone formula is supplied. -/
theorem actual_finite_full_cone_transfers_to_source_realization
    (hvertex : rationalImageNormal H I.equation (Fin.last 3) = 0)
    (hdata : ActualFiniteAffineFullConeExists H I p hY h hh hH e₀ hd hind hGauss)
    (e : RatFunc K ≃ₐ[K] C₀) (f : S₀ →ₐ[K] G) (g : C₀ →ₐ[K] E)
    (hg : ∀ c : C₀, algebraMap E G (g c) = f (c : S₀))
    (z : Fin 4 → G) (hf : ∀ i, f (rationalCoordinate (K := K) i) = z i)
    (y : Fin 4 → E) (hout : ∀ i, aeval z (H i) = algebraMap E G (y i)) :
    RealizedAffineFixedVertexFullCone H I e g z d := by
  obtain ⟨V, hV, hrest⟩ := hdata
  let : Algebra (L) V := valuationConstantAlgebra V hV
  let : IsScalarTower (L) V S₀ := valuationConstantScalarTower V hV
  let κ := IsLocalRing.ResidueField V
  let : Algebra K κ := ((algebraMap (L) κ).comp (algebraMap K (L))).toAlgebra
  let : IsScalarTower K (L) κ := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  let g₀ := IsScalarTower.toAlgHom K (L) κ
  obtain ⟨F, hfin, hforms⟩ := hrest
  let : Module.Finite (g₀.comp ((a).comp e₀.toAlgHom)).fieldRange F := hfin
  let : Algebra C₀ F := parameterImageFiniteExtensionAlgebra (a) e₀ g₀ F
  let : Module.Finite C₀ F := parameterImageFiniteExtensionAlgebra_finite (a) e₀ g₀ F
  let : Algebra.IsAlgebraic C₀ F := inferInstance
  obtain ⟨r, hr, hcone⟩ := hforms
  exact affine_full_cone_transfers_to_actual_source_realization
    H I F hH hd hind hGauss hvertex e f g hg z hf y hout r hr hcone

end DimensionFourDependence
