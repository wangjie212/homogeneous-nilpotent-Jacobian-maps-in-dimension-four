import DimensionFourDependence.FiniteChosenRootConstruction
import DimensionFourDependence.OriginalMapNativeRootForms

/-! # The original map constructs the two remaining actual Gauss-root alternatives -/

namespace DimensionFourDependence

open MvPolynomial

universe u

set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 100000

variable {K : Type u} [Field K] [CharZero K]

/-- The original homogeneous nilpotent rank-three nonplanar map of
Gauss dimension one constructs its own finite coefficients, nonzero
native rational root, exact chosen tangent-plane root formula and two
remaining proportional ruling-form cases. Its binary relation and the
independent-branch divisor contradiction are derived, not assumed.
The cases retain the exact scaled-plane power identity or the native
factorization with independent vectors on the actual ruling, whose
distinguished vector spans exactly the actual characteristic line. -/
theorem original_nonplanar_developable_map_constructs_two_gauss_root_alternatives
    (H : Fin 4 → MvPolynomial (Fin 4) K) {d : ℕ} (hd : 0 < d) (hH : IsHomogMap H d)
    (hN : IsNilpotent (jac H)) (hrank : polyRank (jac H) = 3)
    (hind : ¬ ComponentsDependent H) (I : ImageRelationWitness H)
    (hGauss : gaussImageDimension H I = 1) :
    ∃ (p : Equiv.Perm (Fin 4))
      (hY : AlgebraicIndependent K (fun i : Fin 3 => algebraMap (MvPolynomial (Fin 4) K)
        (FractionRing (MvPolynomial (Fin 4) K)) (H (p i.castSucc))))
      (h : coefficientField (K := K) (fun i : Fin 3 => algebraMap (MvPolynomial (Fin 4) K)
        (FractionRing (MvPolynomial (Fin 4) K)) (H (p i.castSucc))))
      (hh : (h : FractionRing (MvPolynomial (Fin 4) K)) = algebraMap (MvPolynomial (Fin 4) K)
        (FractionRing (MvPolynomial (Fin 4) K)) (H (p 3)))
      (e : RatFunc K ≃ₐ[K] closedGaussParameterField H I),
      ActualFiniteChosenGaussRootAlternativesExist H I p hY h hh hH e hd hind hGauss := by
  obtain ⟨p, hY, h, hh, e, hdata⟩ :=
    original_nonplanar_developable_map_constructs_native_gauss_root_forms H hd hH hN hrank hind I hGauss
  exact ⟨p, hY, h, hh, e,
    actual_finite_native_root_forms_construct_two_chosen_ruling_alternatives H I p hY h hh hH e hd hind hGauss hdata⟩

end DimensionFourDependence
