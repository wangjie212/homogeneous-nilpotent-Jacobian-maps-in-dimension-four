import DimensionFourDependence.ProjectiveClosureRestrictCoefficients
import DimensionFourDependence.SegreProjectiveBoundaryEquations
import DimensionFourDependence.SegreOriginalFiberWitness

/-! # The original radial-product Hessian vanishes at every realized Segre boundary point -/

namespace DimensionFourDependence

open MvPolynomial Matrix
attribute [local instance] coefficientFieldScalarTower MvPolynomial.gradedAlgebra

set_option maxHeartbeats 3000000
set_option synthInstance.maxHeartbeats 100000

variable {K E G κ : Type*} [Field K] [CharZero K] [Field E] [Algebra K E]
    [Field G] [Algebra E G] [Field κ] [Algebra E κ]
local notation "S₀" => FractionRing (MvPolynomial (Fin 4) K)

/-- An actual realization of the original Segre fiber coefficients
forces the exact mapped original Hessian of `Y₀*c` to vanish on every
actual projective boundary direction. No extension of its derivations
to the geometric constants, boundary equation or valuation lift is supplied. -/
theorem segre_realized_projective_boundary_radial_product_hessian_zero
    (Y : Fin 3 → S₀) (hY : AlgebraicIndependent K Y)
    (c q k : coefficientField (K := K) Y) (x : Fin 4 → G) (y : Fin 4 → E)
    (R : FiberCoefficientRealization (Equiv.refl (Fin 4)) Y hY
      (segreGraphFunction (coefficientCoordinate (K := K) Y)) c q k x y)
    (z : Option (Fin 4) → κ) (hz : z ≠ 0)
    (hboundary : projectiveFieldPoint (E := E) z hz ∈ projectiveClosureSet (L := E) x)
    (hz0 : z none = 0) :
    matrixBilinearPairing ((coefficientHessian Y hY
      (coefficientCoordinate (K := K) Y 0 * c)).map ((algebraMap E κ).comp R.coefficientMap))
        (fun i : Fin 3 => z (some i.castSucc)) (fun i : Fin 3 => z (some i.castSucc)) = 0 := by
  let L := coefficientField (K := K) Y
  let U : Fin 3 → L := coefficientCoordinate (K := K) Y
  let δ : Fin 3 → Derivation K L L := coefficientPartial Y hY
  let : Algebra L E := R.coefficientMap.toAlgebra
  let : Algebra L G := ((algebraMap E G).comp R.coefficientMap).toAlgebra
  let : IsScalarTower L E G := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  let : Algebra L κ := ((algebraMap E κ).comp R.coefficientMap).toAlgebra
  let : IsScalarTower L E κ := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  have hbd := projective_closure_point_restrict_coefficients (C := L) x z hz hboundary
  have hU0 : U 0 ≠ 0 := by
    intro he
    apply (hY.transcendental 0).ne_zero
    simpa only [U, coefficientCoordinate_coe, IntermediateField.coe_zero] using
      congrArg (fun a : L => (a : S₀)) he
  have hcoord (i j : Fin 3) : δ i (U j) = if j = i then 1 else 0 :=
    coefficientPartial_coordinate Y hY i j
  have hQ : aeval (x ∘ Fin.castSucc) (quadraticFiberPolynomial (fun i => δ i c)
      (derivationHessian δ (segreGraphFunction U)) q) = 0 := by
    rw [quadraticFiberPolynomial_aeval]
    exact sub_eq_zero.mpr R.quadratic_equation.symm
  have hC : aeval (x ∘ Fin.castSucc) (cubicFiberPolynomial (fun i => δ i q)
      (derivationHessian δ c) (derivationCubicTensor δ (segreGraphFunction U)) k) = 0 := by
    rw [cubicFiberPolynomial_aeval]
    have he := R.cubic_equation
    rw [cubicFiberPolynomial_aeval] at he
    exact he
  exact (segre_graph_projective_boundary_equations δ U hcoord hU0 x z hz hbd hz0
    Fin.castSucc c q k hQ hC).2

/-- The same exact original radial-product Hessian vanishes on the
normalized original coordinates of every actual projective infinity prime. -/
theorem segre_realized_projective_prime_radial_product_hessian_zero
    (Y : Fin 3 → S₀) (hY : AlgebraicIndependent K Y)
    (c q k : coefficientField (K := K) Y) (x : Fin 4 → G) (y : Fin 4 → E)
    (R : FiberCoefficientRealization (Equiv.refl (Fin 4)) Y hY
      (segreGraphFunction (coefficientCoordinate (K := K) Y)) c q k x y)
    (p : ProjectiveSpectrum (homogeneousSubmodule (Option (Fin 4)) E))
    (hboundary : p ∈ projectiveClosureSet (L := E) x)
    (hinfty : X none ∈ p.asHomogeneousIdeal) (a : Fin 4)
    (ha : X (some a) ∉ p.asHomogeneousIdeal) :
    matrixBilinearPairing ((coefficientHessian Y hY
      (coefficientCoordinate (K := K) Y 0 * c)).map
        ((algebraMap E (projectivePrimeRatioField p (some a))).comp R.coefficientMap))
          (fun i : Fin 3 => projectivePrimeRatioCoordinate p (some a) (some i.castSucc))
          (fun i : Fin 3 => projectivePrimeRatioCoordinate p (some a) (some i.castSucc)) = 0 := by
  apply segre_realized_projective_boundary_radial_product_hessian_zero Y hY c q k x y R
    (projectivePrimeRatioCoordinate p (some a)) (projectivePrimeRatioCoordinate_ne_zero p (some a) ha)
  · rw [projectivePrimeRatioCoordinate_represents p (some a) ha]
    exact hboundary
  · exact projectivePrimeRatioCoordinate_zero_of_mem p (some a) none hinfty

end DimensionFourDependence
