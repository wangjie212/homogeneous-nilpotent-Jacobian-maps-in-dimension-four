import DimensionFourDependence.FixedCovectorCoordinateChoice
import DimensionFourDependence.RationalParameterDerivation

/-! # Vertex-preserving coordinate changes commute with the actual vertex partial

The constructed block matrices are independent of the vertex coordinate
and fix it. The polynomial chain rule and original fraction representation
therefore give commutation with the vertex partial on the entire actual
source field, not only its coordinate generators.
-/

namespace DimensionFourDependence

open MvPolynomial Matrix

set_option maxHeartbeats 3000000
set_option synthInstance.maxHeartbeats 100000

variable {K : Type*} [Field K] {n : ℕ}

/-- The actual constant block substitution commutes with the original
polynomial derivative in the fixed vertex coordinate. -/
theorem vertex_preserving_polynomial_pullback_pderiv
    (T : Matrix (Fin n) (Fin n) K) (p : MvPolynomial (Fin (n + 1)) K) :
    pderiv (Fin.last n) (linearPolynomialPullback (vertexPreservingMatrix T) p) =
      linearPolynomialPullback (vertexPreservingMatrix T) (pderiv (Fin.last n) p) := by
  classical
  have hder (i : Fin (n + 1)) :
      pderiv (Fin.last n) (linearPolynomialMap (vertexPreservingMatrix T) i) =
        if i = Fin.last n then 1 else 0 := by
    have he := congrFun (congrFun (jac_linearPolynomialMap (vertexPreservingMatrix T)) i) (Fin.last n)
    change pderiv (Fin.last n) (linearPolynomialMap (vertexPreservingMatrix T) i) =
      C (vertexPreservingMatrix T i (Fin.last n)) at he
    rw [he]
    refine Fin.lastCases ?_ (fun i => ?_) i <;> simp [vertexPreservingMatrix]
  rw [linearPolynomialPullback, pderiv_aeval]
  simp [hder, linearPolynomialPullback]

/-- The same original source-field automorphism commutes with the
actual rational vertex derivative on every source rational function. -/
theorem vertex_preserving_source_fraction_partial
    (T S : Matrix (Fin n) (Fin n) K)
    (hTS : vertexPreservingMatrix T * vertexPreservingMatrix S = 1)
    (hST : vertexPreservingMatrix S * vertexPreservingMatrix T = 1)
    (r : FractionRing (MvPolynomial (Fin (n + 1)) K)) :
    rationalPartial (K := K) (Fin.last n)
      (matrixSourceFractionEquiv (vertexPreservingMatrix T) (vertexPreservingMatrix S) hTS hST r) =
      matrixSourceFractionEquiv (vertexPreservingMatrix T) (vertexPreservingMatrix S) hTS hST
        (rationalPartial (K := K) (Fin.last n) r) := by
  obtain ⟨p, q, _hq, rfl⟩ := IsFractionRing.div_surjective
    (A := MvPolynomial (Fin (n + 1)) K) r
  simp only [map_div₀, Derivation.leibniz_div, smul_eq_mul,
    matrixSourceFractionEquiv_polynomial, rationalPartial_polynomial,
    vertex_preserving_polynomial_pullback_pderiv, map_mul, map_sub, map_pow, map_inv₀]

end DimensionFourDependence
