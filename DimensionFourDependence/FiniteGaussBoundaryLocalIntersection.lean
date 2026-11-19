import DimensionFourDependence.FiniteRulingSimpleHessian
import DimensionFourDependence.ParametricModifiedQuadricJets
import DimensionFourDependence.RulingBoundaryBasis
import DimensionFourDependence.RankOneBoundaryChart

/-! # The actual Gauss boundary equations construct their length-two local intersection

The finite ruling dual and original nonzero normal construct an
invertible infinity chart. The original graph Hessian turns its first
leading boundary equation into a nonzero scalar multiple of u^2.
The root equation gives a simple zero of the actual modified second
leading equation. Their full pair ideal therefore has an actual
quotient localization of dimension and intersection length exactly two.

This constructs the local intersection of the actual leading equations.
Identifying the fiber's infinity stalk as a quotient of this algebra,
and relating its local length to the global graded section, remain separate.
-/

namespace DimensionFourDependence

open MvPolynomial Matrix Module

variable {F : Type*} [Field F]

/-- Exact local multiplicity two for the actual polynomial pair ideal
at its constructed rational-origin prime. -/
noncomputable def HasOriginLocalIntersectionMultiplicityTwo (J : Ideal (MvPolynomial (Fin 2) F)) : Prop :=
  ∃ hJ : J ≤ RingHom.ker (aeval (fun _ : Fin 2 => (0 : F))).toRingHom,
    let R := Localization.AtPrime (zeroPointQuotientPrime J hJ)
    Module.Finite F R ∧ finrank F R = 2 ∧ Module.length R R = 2

/-- The exact first equation and original simple transverse second
equation construct the local multiplicity of their full actual pair ideal. -/
theorem boundary_pair_actual_local_multiplicity_two
    (Q P : MvPolynomial (Fin 2) F) (scalar : F) (hscalar : scalar ≠ 0)
    (hQ : Q = C scalar * X 0 ^ 2)
    (hP : aeval (fun _ : Fin 2 => (0 : F)) P = 0)
    (hPv : aeval (fun _ : Fin 2 => (0 : F)) (pderiv 1 P) ≠ 0) :
    HasOriginLocalIntersectionMultiplicityTwo (Ideal.span ({Q, P} : Set (MvPolynomial (Fin 2) F))) := by
  have hI : Ideal.span ({Q, P} : Set (MvPolynomial (Fin 2) F)) = simplePolynomialIntersectionIdeal P := by
    rw [hQ]
    exact scaled_coordinate_square_pair_ideal scalar hscalar P
  rw [hI]
  exact ⟨simplePolynomialIntersectionIdeal_origin P hP,
    simple_polynomial_intersection_local_exact_multiplicity_two P hP hPv⟩

variable {K : Type*} [Field K] [CharZero K] [Algebra K F]

/-- The actual graph and finite root data construct their own
invertible chart and exact length-two intersection of the original
first and modified second leading boundary equations. -/
theorem finite_parameter_graph_constructs_actual_simple_boundary_intersection
    (p : RatFunc K →ₐ[K] F) (delta : Fin 3 → Derivation K F F) (y : Fin 3 → F)
    (hcoord : ∀ i j, delta i (y j) = if j = i then 1 else 0)
    (hcomm : ∀ i j a, delta i (delta j a) = delta j (delta i a))
    (A : Fin 3 → RatFunc K)
    (htangent : (fun i => p (rationalParameterDerivative K (A i))) ⬝ᵥ y = 0)
    (hfirst : (fun i => p (rationalParameterDerivative K (A i))) ≠ 0)
    (h : F) (hgradient : ∀ i, delta i h = p (A i))
    (C : IntermediateField p.fieldRange F) [Module.Finite p.fieldRange C]
    (m s : Fin 3 → C)
    (hpair : LinearIndependent C ![rulingFormRestriction (finiteParameterGraphRuling p C A) m,
      rulingFormRestriction (finiteParameterGraphRuling p C A) s])
    {d : ℕ} (hd : 0 < d) (rho c q : F) (hrho : rho ≠ 0)
    (hfactor : parametricRulingDenominator p A y * c = ((fun i => (m i : F)) ⬝ᵥ y) * rho)
    (hroot : rho ^ d = (fun i => (s i : F)) ⬝ᵥ y) :
    ∃ w z b : Fin 3 → C,
      finiteParameterGraphNormal p C A ⬝ᵥ w = 1 ∧
      b ∈ finiteParameterGraphRuling p C A ∧ z ∈ finiteParameterGraphRuling p C A ∧
      m ⬝ᵥ b = 1 ∧ s ⬝ᵥ b = 0 ∧ m ⬝ᵥ z = 0 ∧ s ⬝ᵥ z = 1 ∧
      (rulingBoundaryCoordinateMatrix w z b).det ≠ 0 ∧
      (rulingBoundaryCoordinateMatrix (fun i => (w i : F)) (fun i => (z i : F)) (fun i => (b i : F))).det ≠ 0 ∧
      let chart := boundaryAffineChartCoordinate (fun i => (b i : F)) (fun i => (w i : F)) (fun i => (z i : F))
      let P := aeval chart (modifiedBoundaryQuadric (fun i => delta i c)
        (parametricGraphCubicCovector p A y) (derivationHessian delta c))
      let Q := aeval chart (homogeneousComponent 2 (quadraticFiberPolynomial (fun i => delta i c) (derivationHessian delta h) q))
      aeval (fun _ : Fin 2 => (0 : F)) P = 0 ∧
        aeval (fun _ : Fin 2 => (0 : F)) (pderiv 1 P) ≠ 0 ∧
        Q = MvPolynomial.C ((2 : F)⁻¹ * (-(parametricRulingDenominator p A y)⁻¹)) * X 0 ^ 2 ∧
        Ideal.span ({Q, P} : Set (MvPolynomial (Fin 2) F)) = simplePolynomialIntersectionIdeal P ∧
        HasOriginLocalIntersectionMultiplicityTwo (Ideal.span ({Q, P} : Set (MvPolynomial (Fin 2) F))) := by
  let : CharZero F := charZero_of_injective_algebraMap (algebraMap K F).injective
  obtain ⟨b, z, _hLI, hb, hz, hMb, hSb, hMz, hSz, hself, _hvalue, hmixed⟩ :=
    finite_parameter_graph_constructs_simple_root_hessian_pair p delta y hcoord A htangent hfirst
      C m s hpair hd rho c hrho hfactor hroot
  have hab : finiteParameterGraphNormal p C A ⬝ᵥ b = 0 := hb
  have haz : finiteParameterGraphNormal p C A ⬝ᵥ z = 0 := hz
  obtain ⟨w, hw, hdet⟩ := exists_ruling_boundary_coordinate_matrix (finiteParameterGraphNormal p C A)
    m s z b (finiteParameterGraphNormal_ne_zero p C A hfirst) haz hab hMz hMb hSz hSb
  have hdetF : (rulingBoundaryCoordinateMatrix (fun i => (w i : F))
      (fun i => (z i : F)) (fun i => (b i : F))).det ≠ 0 := by
    change (rulingBoundaryCoordinateMatrix (fun i => algebraMap C F (w i))
      (fun i => algebraMap C F (z i)) (fun i => algebraMap C F (b i))).det ≠ 0
    exact rulingBoundaryCoordinateMatrix_map_det_ne_zero w z b hdet
  have hwF : (fun i => p (rationalParameterDerivative K (A i))) ⬝ᵥ (fun i => (w i : F)) = 1 := by
    have he := congrArg (algebraMap C F) hw
    simpa only [dotProduct, map_sum, map_mul, map_one, IntermediateField.algebraMap_apply,
      finiteParameterGraphNormal_value] using he
  have hbF := finiteParameterGraphRuling_original_pairing p C A b hb
  have hzF := finiteParameterGraphRuling_original_pairing p C A z hz
  let chart := boundaryAffineChartCoordinate (fun i => (b i : F)) (fun i => (w i : F)) (fun i => (z i : F))
  let P : MvPolynomial (Fin 2) F := aeval chart (modifiedBoundaryQuadric (fun i => delta i c)
    (parametricGraphCubicCovector p A y) (derivationHessian delta c))
  let Q : MvPolynomial (Fin 2) F := aeval chart
    (homogeneousComponent 2 (quadraticFiberPolynomial (fun i => delta i c) (derivationHessian delta h) q))
  let scalar : F := (2 : F)⁻¹ * (-(parametricRulingDenominator p A y)⁻¹)
  have hscalar : scalar ≠ 0 := mul_ne_zero (inv_ne_zero (by norm_num : (2 : F) ≠ 0))
    (neg_ne_zero.mpr (inv_ne_zero (parametric_ruling_denominator_ne_zero p delta y hcoord A htangent hfirst)))
  have hjet : aeval (fun _ : Fin 2 => (0 : F)) P = 0 ∧
      aeval (fun _ : Fin 2 => (0 : F)) (pderiv 1 P) ≠ 0 :=
    parametric_modified_quadric_constructs_simple_chart_root p delta y hcoord hcomm A htangent hfirst
      (fun i => (b i : F)) (fun i => (w i : F)) (fun i => (z i : F)) hbF hzF
      (fun i => finite_parameter_extension_coefficient_algebraic p C (b i)) c hself hmixed
  have hQ : Q = MvPolynomial.C scalar * X 0 ^ 2 :=
    parametric_graph_first_boundary_chart p delta y hcoord A htangent hfirst h hgradient
      (fun i => (b i : F)) (fun i => (w i : F)) (fun i => (z i : F)) (fun i => delta i c) q hbF hwF hzF
  have hI : Ideal.span ({Q, P} : Set (MvPolynomial (Fin 2) F)) = simplePolynomialIntersectionIdeal P := by
    rw [hQ]
    exact scaled_coordinate_square_pair_ideal scalar hscalar P
  refine ⟨w, z, b, hw, hb, hz, hMb, hSb, hMz, hSz, hdet, hdetF, ?_⟩
  exact ⟨hjet.1, hjet.2, hQ, hI, boundary_pair_actual_local_multiplicity_two Q P scalar hscalar hQ hjet.1 hjet.2⟩

end DimensionFourDependence
