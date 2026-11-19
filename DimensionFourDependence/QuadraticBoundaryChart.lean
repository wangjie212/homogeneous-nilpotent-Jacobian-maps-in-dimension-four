import DimensionFourDependence.ModifiedCubicFiberBoundary
import DimensionFourDependence.IsotropicQuadraticCoordinates

/-! # Original quadratic boundary equations in an affine infinity chart

The chart is the original vector b+u w+v z. Evaluating at its origin
retains b, and its transverse first derivative retains z. The two
quadratic and linear-factor contributions to the modified cubic's
actual leading equation therefore have explicit original Hessian
pairings and covector pairings.
-/

namespace DimensionFourDependence

open MvPolynomial Matrix

variable {F : Type*} [Field F] {n : ℕ}

/-- Original coordinate expressions in the affine chart at b, with
normal coordinate u and transverse ruling coordinate v. -/
noncomputable def boundaryAffineChartCoordinate (b w z : Fin n → F) :
    Fin n → MvPolynomial (Fin 2) F :=
  fun i => C (b i) + C (w i) * X 0 + C (z i) * X 1

/-- The actual modified cubic's degree-two boundary equation. -/
noncomputable def modifiedBoundaryQuadric (g Lambda : Fin n → F)
    (S : Matrix (Fin n) (Fin n) F) : MvPolynomial (Fin n) F :=
  -C 3 * quadraticFormPolynomial S + C 2 * linearFormPolynomial Lambda * linearFormPolynomial g

/-- This is the leading equation of the original modified cubic,
independently of its lower-order invariant constants. -/
theorem modifiedBoundaryQuadric_eq_leading_component
    (g v Lambda : Fin n → F) (S : Matrix (Fin n) (Fin n) F) (q k : F) :
    homogeneousComponent 2 (modifiedCubicFiberPolynomial g v Lambda S q k) =
      modifiedBoundaryQuadric g Lambda S :=
  modifiedCubicFiberPolynomial_leading_component g v Lambda S q k

/-- The original linear covector in this chart has its three exact
original pairings as coefficients. -/
theorem boundary_chart_linear_form (a b w z : Fin n → F) :
    aeval (boundaryAffineChartCoordinate b w z) (linearFormPolynomial a) =
      C (a ⬝ᵥ b) + C (a ⬝ᵥ w) * X 0 + C (a ⬝ᵥ z) * X 1 := by
  simp only [linearFormPolynomial, map_sum, map_mul, aeval_C, aeval_X,
    boundaryAffineChartCoordinate, MvPolynomial.algebraMap_eq, dotProduct, map_sum, map_mul,
    mul_add, Finset.sum_add_distrib, Finset.sum_mul, mul_assoc]

/-- The origin value of a charted original linear covector. -/
theorem boundary_chart_linear_origin (a b w z : Fin n → F) :
    aeval (fun _ : Fin 2 => (0 : F))
      (aeval (boundaryAffineChartCoordinate b w z) (linearFormPolynomial a)) = a ⬝ᵥ b := by
  rw [boundary_chart_linear_form]
  simp

/-- The transverse derivative of a charted original linear covector. -/
theorem boundary_chart_linear_transverse (a b w z : Fin n → F) :
    aeval (fun _ : Fin 2 => (0 : F))
      (pderiv 1 (aeval (boundaryAffineChartCoordinate b w z) (linearFormPolynomial a))) = a ⬝ᵥ z := by
  rw [boundary_chart_linear_form]
  simp [pderiv_X]

/-- The original quadratic form at the chart origin is its original
self-pairing at the fixed vector b. -/
theorem boundary_chart_quadratic_origin (S : Matrix (Fin n) (Fin n) F) (b w z : Fin n → F) :
    aeval (fun _ : Fin 2 => (0 : F))
      (aeval (boundaryAffineChartCoordinate b w z) (quadraticFormPolynomial S)) =
        matrixBilinearPairing S b b := by
  simp [quadraticFormPolynomial, boundaryAffineChartCoordinate, matrixBilinearPairing]

/-- The transverse derivative of the original quadratic is the sum
of its two original ordered mixed pairings. -/
theorem boundary_chart_quadratic_transverse (S : Matrix (Fin n) (Fin n) F) (b w z : Fin n → F) :
    aeval (fun _ : Fin 2 => (0 : F))
      (pderiv 1 (aeval (boundaryAffineChartCoordinate b w z) (quadraticFormPolynomial S))) =
        matrixBilinearPairing S z b + matrixBilinearPairing S b z := by
  simp [quadraticFormPolynomial, boundaryAffineChartCoordinate, MvPolynomial.algebraMap_eq,
    pderiv_X, matrixBilinearPairing, Finset.sum_add_distrib, mul_add, add_mul, mul_assoc]

/-- The original modified leading equation at the actual chart origin. -/
theorem boundary_chart_modified_origin
    (g Lambda b w z : Fin n → F) (S : Matrix (Fin n) (Fin n) F) :
    aeval (fun _ : Fin 2 => (0 : F))
      (aeval (boundaryAffineChartCoordinate b w z) (modifiedBoundaryQuadric g Lambda S)) =
        -3 * matrixBilinearPairing S b b + 2 * (Lambda ⬝ᵥ b) * (g ⬝ᵥ b) := by
  simp only [modifiedBoundaryQuadric, map_add, map_mul, map_neg, aeval_C]
  rw [boundary_chart_quadratic_origin, boundary_chart_linear_origin, boundary_chart_linear_origin]
  simp

/-- The transverse derivative of the actual modified leading equation,
with every original ordered Hessian and covector contribution retained. -/
theorem boundary_chart_modified_transverse
    (g Lambda b w z : Fin n → F) (S : Matrix (Fin n) (Fin n) F) :
    aeval (fun _ : Fin 2 => (0 : F))
      (pderiv 1 (aeval (boundaryAffineChartCoordinate b w z) (modifiedBoundaryQuadric g Lambda S))) =
        -3 * (matrixBilinearPairing S z b + matrixBilinearPairing S b z) +
          2 * ((Lambda ⬝ᵥ z) * (g ⬝ᵥ b) + (Lambda ⬝ᵥ b) * (g ⬝ᵥ z)) := by
  let Q := aeval (boundaryAffineChartCoordinate b w z) (quadraticFormPolynomial S)
  let L := aeval (boundaryAffineChartCoordinate b w z) (linearFormPolynomial Lambda)
  let G := aeval (boundaryAffineChartCoordinate b w z) (linearFormPolynomial g)
  have hchart : aeval (boundaryAffineChartCoordinate b w z) (modifiedBoundaryQuadric g Lambda S) =
      -C (3 : F) * Q + C (2 : F) * (L * G) := by
    simp only [modifiedBoundaryQuadric, map_add, map_mul, map_neg, aeval_C, MvPolynomial.algebraMap_eq]
    dsimp only [Q, L, G]
    ring
  have hneg (P : MvPolynomial (Fin 2) F) :
      aeval (fun _ : Fin 2 => (0 : F)) (pderiv 1 (-C (3 : F) * P)) =
        -3 * aeval (fun _ : Fin 2 => (0 : F)) (pderiv 1 P) := by simp
  have hprod (P R : MvPolynomial (Fin 2) F) :
      aeval (fun _ : Fin 2 => (0 : F)) (pderiv 1 (C (2 : F) * (P * R))) =
        2 * (aeval (fun _ : Fin 2 => (0 : F)) (pderiv 1 P) * aeval (fun _ : Fin 2 => (0 : F)) R +
          aeval (fun _ : Fin 2 => (0 : F)) P * aeval (fun _ : Fin 2 => (0 : F)) (pderiv 1 R)) := by
    simp only [pderiv_mul, map_add, map_mul]
    simp
  rw [hchart]
  simp only [map_add, hneg, hprod]
  rw [show Q = aeval (boundaryAffineChartCoordinate b w z) (quadraticFormPolynomial S) from rfl,
    show L = aeval (boundaryAffineChartCoordinate b w z) (linearFormPolynomial Lambda) from rfl,
    show G = aeval (boundaryAffineChartCoordinate b w z) (linearFormPolynomial g) from rfl,
    boundary_chart_quadratic_transverse, boundary_chart_linear_transverse,
    boundary_chart_linear_transverse, boundary_chart_linear_origin, boundary_chart_linear_origin]

end DimensionFourDependence
