import DimensionFourDependence.NormalizedProjectivePointLift
import DimensionFourDependence.ActualInfinityPrimeAlgebraicity
import DimensionFourDependence.CompatibleExtensionBoundaryTransport

/-! # A specified boundary lifts to algebraic original graph coordinates -/

namespace DimensionFourDependence

open MvPolynomial

attribute [local instance] MvPolynomial.gradedAlgebra coefficientFieldScalarTower

universe u

attribute [local instance] coefficientFieldScalarTower

set_option maxHeartbeats 3000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 100000
set_option quotPrecheck false

variable {K : Type u} [Field K] [CharZero K]
    (H : Fin 4 → MvPolynomial (Fin 4) K) (hrank : polyRank (jac H) = 3)
    (p : Equiv.Perm (Fin 4))
    (hY : AlgebraicIndependent K (fun i : Fin 3 => algebraMap (MvPolynomial (Fin 4) K)
      (FractionRing (MvPolynomial (Fin 4) K)) (H (p i.castSucc))))

local notation "S₀" => FractionRing (MvPolynomial (Fin 4) K)
local notation "Y" => fun i : Fin 3 => algebraMap (MvPolynomial (Fin 4) K) S₀ (H (p i.castSucc))
local notation "L" => coefficientField (K := K) (Y)
local notation "x" => rationalCoordinate (K := K) (n := 4)

include hrank

/-- Lift the same specified boundary to a compatible algebraic graph
coefficient field and construct its actual normalized algebraic coordinate
field. Exact contraction retains the original point, and its original
source-coordinate label remains the unit frame. -/
theorem compatible_original_graph_boundary_lift_constructs_algebraic_coordinates
    (I : ImageRelationWitness H) {d : ℕ} (hd : 0 < d) (hH : IsHomogMap H d)
    (hN : IsNilpotent (jac H)) (hind : ¬ComponentsDependent H) (hGauss : gaussImageDimension H I = 1)
    (h c qinv : L) (hh : (h : S₀) = algebraMap (MvPolynomial (Fin 4) K) S₀ (H (p 3)))
    (hc : (c : S₀) = firstFiberInvariantInChart p (Y) hY h)
    (hqinv : (qinv : S₀) = secondFiberInvariant p (Y) hY h c)
    {C A G : Type u} [Field C] [Field A] [Field G]
    [Algebra C A] [Algebra A G] [Algebra C G] [IsScalarTower C A G] [Algebra.IsAlgebraic C A]
    (v : Fin 4 → G) (Φ : S₀ →+* G) (g : (L) →+* A)
    (hg : ∀ l : L, algebraMap A G (g l) = Φ (l : S₀))
    (hcoords : ∀ i, Φ ((x) i) = v i)
    (halg : letI : Algebra (L) A := g.toAlgebra; Algebra.IsAlgebraic (L) A)
    (p₀ : ProjectiveSpectrum (homogeneousSubmodule (Option (Fin 4)) C))
    (hp : p₀ ∈ projectiveClosureSet («L» := C) v)
    (hp0 : X none ∈ p₀.asHomogeneousIdeal) (a : Fin 4) (hpa : X (some a) ∉ p₀.asHomogeneousIdeal) :
    letI : Algebra (L) A := g.toAlgebra
    letI : SMul (L) A := g.toAlgebra.toSMul
    ∃ Q : ProjectiveSpectrum (homogeneousSubmodule (Option (Fin 4)) A),
      letI : Algebra A (projectivePrimeRatioField Q (some a)) :=
        projectivePrimeRatioFieldCoefficientAlgebra Q (some a)
      letI : SMul A (projectivePrimeRatioField Q (some a)) :=
        (projectivePrimeRatioFieldCoefficientAlgebra Q (some a)).toSMul
      ∃ hQa : X (some a) ∉ Q.asHomogeneousIdeal,
        (letI : Algebra C (projectivePrimeRatioField Q (some a)) :=
          ((algebraMap A (projectivePrimeRatioField Q (some a))).comp (algebraMap C A)).toAlgebra;
          (projectiveFieldPointIdeal (E := C) (projectivePrimeRatioCoordinate Q (some a))).toIdeal =
            p₀.asHomogeneousIdeal.toIdeal) ∧
        letI : Algebra (L) (projectivePrimeRatioField Q (some a)) :=
          ((algebraMap A (projectivePrimeRatioField Q (some a))).comp g).toAlgebra
        letI : SMul (L) (projectivePrimeRatioField Q (some a)) :=
          (((algebraMap A (projectivePrimeRatioField Q (some a))).comp g).toAlgebra).toSMul
        Algebra.IsAlgebraic (L) (projectivePrimeRatioField Q (some a)) ∧
        projectiveFieldPoint (E := L) (projectivePrimeRatioCoordinate Q (some a))
          (projectivePrimeRatioCoordinate_ne_zero Q (some a) hQa) ∈ projectiveClosureSet («L» := L) (x) ∧
        projectivePrimeRatioCoordinate Q (some a) none = 0 ∧
        projectivePrimeRatioCoordinate Q (some a) (some a) = 1 := by
  letI : Algebra (L) A := g.toAlgebra
  letI : SMul (L) A := g.toAlgebra.toSMul
  obtain ⟨Q, _hcontract, hQ0, hQa, hQideal, hpointA, hQzero, hQframe⟩ :=
    specified_projective_infinity_lifts_with_same_original_coordinate_ideal (A := A) v p₀ hp hp0 a hpa
  letI : Algebra A (projectivePrimeRatioField Q (some a)) :=
    projectivePrimeRatioFieldCoefficientAlgebra Q (some a)
  letI : SMul A (projectivePrimeRatioField Q (some a)) :=
    (projectivePrimeRatioFieldCoefficientAlgebra Q (some a)).toSMul
  letI : Algebra (L) (projectivePrimeRatioField Q (some a)) :=
    ((algebraMap A (projectivePrimeRatioField Q (some a))).comp g).toAlgebra
  letI : SMul (L) (projectivePrimeRatioField Q (some a)) :=
    (((algebraMap A (projectivePrimeRatioField Q (some a))).comp g).toAlgebra).toSMul
  letI : IsScalarTower (L) A (projectivePrimeRatioField Q (some a)) := IsScalarTower.of_algebraMap_eq' rfl
  have hpointL := compatible_source_extension_boundary_mem_original_coefficient_closure
    («L» := L) (S := S₀) (B := A) (Z := G) (T := projectivePrimeRatioField Q (some a)) Φ g (x) v
    (fun l => (hg l).symm) hcoords (projectivePrimeRatioCoordinate Q (some a))
    (projectivePrimeRatioCoordinate_ne_zero Q (some a) hQa) hpointA
  letI : Algebra K A := (g.comp (algebraMap K (L))).toAlgebra
  letI : IsScalarTower K (L) A := IsScalarTower.of_algebraMap_eq' rfl
  have hExt := normalized_projective_prime_contains_extended_original_cone
    («L» := L) (F := A) (κ := S₀) (x) Q (some a) hQa hpointL
  have hRalg := actual_full_infinity_prime_normalized_field_isAlgebraic H hrank p hY A
    hd hH hN hind I hGauss h c qinv hh hc hqinv Q hExt hQ0 a hQa
  letI : Algebra.IsAlgebraic A (projectivePrimeRatioField Q (some a)) := hRalg
  letI : Algebra.IsAlgebraic (L) A := halg
  exact ⟨Q, hQa, hQideal, Algebra.IsAlgebraic.trans (L) A (projectivePrimeRatioField Q (some a)),
    hpointL, hQzero, hQframe⟩

end DimensionFourDependence
