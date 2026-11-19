import DimensionFourDependence.RulingMixedDerivative
import DimensionFourDependence.QuadraticBoundaryChart

/-! # The original modified quadric has a simple transverse chart root

The actual normal-derivative formula identifies the modified leading
quadric with the Hessian of nc on the original ruling. In an affine
chart at a fixed root, its transverse derivative is -6/n times the
original mixed Hessian pairing. The constructed nonzero mixed pairing
therefore supplies the simple-root condition for the polynomial local
intersection theorem.
-/

namespace DimensionFourDependence

open MvPolynomial Matrix

variable {K F : Type*} [Field K] [CharZero K] [Field F] [Algebra K F] {n : ℕ}

/-- The actual Hessian of nc retains both denominator-gradient cross
terms on two parameter-defined ruling directions. -/
theorem parametric_ruling_product_hessian_pairing
    (p : RatFunc K →ₐ[K] F) (delta : Fin n → Derivation K F F) (y : Fin n → F)
    (hcoord : ∀ i j, delta i (y j) = if j = i then 1 else 0)
    (A : Fin n → RatFunc K)
    (htangent : (fun i => p (rationalParameterDerivative K (A i))) ⬝ᵥ y = 0)
    (hfirst : (fun i => p (rationalParameterDerivative K (A i))) ≠ 0)
    (v w : Fin n → F)
    (hv : (fun i => p (rationalParameterDerivative K (A i))) ⬝ᵥ v = 0)
    (hw : (fun i => p (rationalParameterDerivative K (A i))) ⬝ᵥ w = 0)
    (halgw : ∀ i, IsAlgebraic p.fieldRange (w i)) (c : F) :
    matrixBilinearPairing (derivationHessian delta (parametricRulingDenominator p A y * c)) v w =
      parametricRulingDenominator p A y * matrixBilinearPairing (derivationHessian delta c) v w +
        ((fun i => p (rationalParameterDerivative K (rationalParameterDerivative K (A i)))) ⬝ᵥ v) *
          ((fun i => delta i c) ⬝ᵥ w) +
        ((fun i => p (rationalParameterDerivative K (rationalParameterDerivative K (A i)))) ⬝ᵥ w) *
          ((fun i => delta i c) ⬝ᵥ v) := by
  have ht : coordinateEuler v delta (p RatFunc.X) = 0 :=
    parametric_ruling_direction_fixes_parameter p delta y hcoord A htangent hfirst v hv
  have hwD (i : Fin n) : coordinateEuler v delta (w i) = 0 :=
    parameter_algebraic_coefficient_direction_constant p (coordinateEuler v delta) ht (w i) (halgw i)
  rw [← coordinate_direction_mixed_derivative delta v w hwD]
  exact parametric_ruling_mixed_product_derivative p delta y hcoord A htangent hfirst v w hv hw halgw c

/-- The actual modified leading quadric at a ruling point is -3/n
times the original Hessian self-pairing of nc. -/
theorem parametric_modified_quadric_chart_origin
    (p : RatFunc K →ₐ[K] F) (delta : Fin n → Derivation K F F) (y : Fin n → F)
    (hcoord : ∀ i j, delta i (y j) = if j = i then 1 else 0)
    (A : Fin n → RatFunc K)
    (htangent : (fun i => p (rationalParameterDerivative K (A i))) ⬝ᵥ y = 0)
    (hfirst : (fun i => p (rationalParameterDerivative K (A i))) ≠ 0)
    (b w z : Fin n → F)
    (hb : (fun i => p (rationalParameterDerivative K (A i))) ⬝ᵥ b = 0)
    (halgb : ∀ i, IsAlgebraic p.fieldRange (b i)) (c : F) :
    aeval (fun _ : Fin 2 => (0 : F)) (aeval (boundaryAffineChartCoordinate b w z)
      (modifiedBoundaryQuadric (fun i => delta i c) (parametricGraphCubicCovector p A y) (derivationHessian delta c))) =
        (-3 : F) / parametricRulingDenominator p A y *
          matrixBilinearPairing (derivationHessian delta (parametricRulingDenominator p A y * c)) b b := by
  have hN := parametric_ruling_denominator_ne_zero p delta y hcoord A htangent hfirst
  have hLambda := parametric_graph_cubic_covector_on_ruling p y A b hb
  have hpair := parametric_ruling_product_hessian_pairing p delta y hcoord A htangent hfirst b b hb hb halgb c
  rw [boundary_chart_modified_origin, hLambda, hpair]
  field_simp
  ring

/-- The actual charted modified quadric's transverse derivative is
-6/n times the original ordered mixed Hessian pairing of nc. -/
theorem parametric_modified_quadric_chart_transverse
    (p : RatFunc K →ₐ[K] F) (delta : Fin n → Derivation K F F) (y : Fin n → F)
    (hcoord : ∀ i j, delta i (y j) = if j = i then 1 else 0)
    (hcomm : ∀ i j a, delta i (delta j a) = delta j (delta i a))
    (A : Fin n → RatFunc K)
    (htangent : (fun i => p (rationalParameterDerivative K (A i))) ⬝ᵥ y = 0)
    (hfirst : (fun i => p (rationalParameterDerivative K (A i))) ≠ 0)
    (b w z : Fin n → F)
    (hb : (fun i => p (rationalParameterDerivative K (A i))) ⬝ᵥ b = 0)
    (hz : (fun i => p (rationalParameterDerivative K (A i))) ⬝ᵥ z = 0)
    (halgb : ∀ i, IsAlgebraic p.fieldRange (b i)) (c : F) :
    aeval (fun _ : Fin 2 => (0 : F)) (pderiv 1 (aeval (boundaryAffineChartCoordinate b w z)
      (modifiedBoundaryQuadric (fun i => delta i c) (parametricGraphCubicCovector p A y) (derivationHessian delta c)))) =
        (-6 : F) / parametricRulingDenominator p A y *
          matrixBilinearPairing (derivationHessian delta (parametricRulingDenominator p A y * c)) z b := by
  have hN := parametric_ruling_denominator_ne_zero p delta y hcoord A htangent hfirst
  have hLb := parametric_graph_cubic_covector_on_ruling p y A b hb
  have hLz := parametric_graph_cubic_covector_on_ruling p y A z hz
  have hsym := matrixBilinearPairing_symmetric (derivationHessian delta c)
    (derivationHessian_symmetric delta hcomm c) b z
  have hpair := parametric_ruling_product_hessian_pairing p delta y hcoord A htangent hfirst z b hz hb halgb c
  rw [boundary_chart_modified_transverse, hsym, hLb, hLz, hpair]
  field_simp
  ring

/-- A fixed Hessian root with a nonzero transverse mixed pairing
gives the actual polynomial simple-root hypotheses in this original chart. -/
theorem parametric_modified_quadric_constructs_simple_chart_root
    (p : RatFunc K →ₐ[K] F) (delta : Fin n → Derivation K F F) (y : Fin n → F)
    (hcoord : ∀ i j, delta i (y j) = if j = i then 1 else 0)
    (hcomm : ∀ i j a, delta i (delta j a) = delta j (delta i a))
    (A : Fin n → RatFunc K)
    (htangent : (fun i => p (rationalParameterDerivative K (A i))) ⬝ᵥ y = 0)
    (hfirst : (fun i => p (rationalParameterDerivative K (A i))) ≠ 0)
    (b w z : Fin n → F)
    (hb : (fun i => p (rationalParameterDerivative K (A i))) ⬝ᵥ b = 0)
    (hz : (fun i => p (rationalParameterDerivative K (A i))) ⬝ᵥ z = 0)
    (halgb : ∀ i, IsAlgebraic p.fieldRange (b i)) (c : F)
    (hself : matrixBilinearPairing (derivationHessian delta (parametricRulingDenominator p A y * c)) b b = 0)
    (hmixed : matrixBilinearPairing (derivationHessian delta (parametricRulingDenominator p A y * c)) z b ≠ 0) :
    let P := aeval (boundaryAffineChartCoordinate b w z)
      (modifiedBoundaryQuadric (fun i => delta i c) (parametricGraphCubicCovector p A y) (derivationHessian delta c))
    aeval (fun _ : Fin 2 => (0 : F)) P = 0 ∧
      aeval (fun _ : Fin 2 => (0 : F)) (pderiv 1 P) ≠ 0 := by
  let : CharZero F := charZero_of_injective_algebraMap (algebraMap K F).injective
  dsimp only
  constructor
  · rw [parametric_modified_quadric_chart_origin p delta y hcoord A htangent hfirst b w z hb halgb c,
      hself, mul_zero]
  · rw [parametric_modified_quadric_chart_transverse p delta y hcoord hcomm A htangent hfirst b w z hb hz halgb c]
    exact mul_ne_zero (div_ne_zero (by norm_num : (-6 : F) ≠ 0)
      (parametric_ruling_denominator_ne_zero p delta y hcoord A htangent hfirst)) hmixed

end DimensionFourDependence
