import DimensionFourDependence.ConstructedConeTangentPolynomials
import DimensionFourDependence.ActualAffineLevelTangent
import DimensionFourDependence.AffineTangentCoefficientDescent

/-! # The actual nilpotent cone formulas construct both constant tangent lifts

The two trace identities construct an actual generic tangent over K(t),
whose horizontal coefficients are independent over K. The exact generic
level relation ideal and polynomial-flow argument give global annihilation.
Linear coefficient functionals then construct both normalized original
constant tangent lifts. No tangent field or slope is assumed.
-/

namespace DimensionFourDependence

open MvPolynomial

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 100000

variable {K F : Type*} [Field K] [CharZero K] [Field F] [Algebra K F]

omit [CharZero K] in
/-- A full parameter-polynomial tangent identity gives tangency of its
literal K(t)-coefficient field at the actual source point t=P(x). -/
theorem polynomial_parameter_tangent_identity_actual_source_value
    (t : F) (x : Fin 3 → F) (P : MvPolynomial (Fin 3) K) (hvalue : t = aeval x P)
    (U : Fin 2 → Polynomial K) (V : Fin 3 → Polynomial K)
    (hidentity : Polynomial.aeval P (U 0) * pderiv 0 P + Polynomial.aeval P (U 1) * pderiv 1 P +
      (Polynomial.aeval P (V 0) + Polynomial.aeval P (V 1) * X 0 +
        Polynomial.aeval P (V 2) * X 1) * pderiv 2 P = 0) :
    aeval x (affineProjectedTangentAction
      (fun i => Polynomial.aeval (IntermediateField.AdjoinSimple.gen K t) (U i))
      (fun i => Polynomial.aeval (IntermediateField.AdjoinSimple.gen K t) (V i))
      (MvPolynomial.map (algebraMap K (IntermediateField.adjoin K {t})) P)) = 0 := by
  have hpoly (Q : MvPolynomial (Fin 3) K) :
      aeval x (MvPolynomial.map (algebraMap K (IntermediateField.adjoin K {t})) Q) = aeval x Q :=
    aeval_map_coefficients x Q
  have hscalar (p : Polynomial K) :
      algebraMap (IntermediateField.adjoin K {t}) F
        (Polynomial.aeval (IntermediateField.AdjoinSimple.gen K t) p) =
      aeval x (Polynomial.aeval P p) := by
    change (IntermediateField.adjoin K {t}).val
      (Polynomial.aeval (IntermediateField.AdjoinSimple.gen K t) p) = _
    rw [← Polynomial.aeval_algHom_apply (IntermediateField.adjoin K {t}).val,
      ← Polynomial.aeval_algHom_apply (aeval x), ← hvalue]
    rfl
  have he := congrArg (aeval x) hidentity
  simp only [map_add, map_mul, aeval_X, map_zero] at he
  simp only [affineProjectedTangentAction, affineTangentVerticalCoefficient, pderiv_map,
    map_add, map_mul, aeval_C, aeval_X, hpoly, hscalar]
  exact he

attribute [-instance] IntermediateField.instSMulSubtypeMem in
/-- The original complete affine cone formulas, nilpotence, an actual
relatively closed primitive parameter and independence of the three
scalar polynomials construct both normalized original-field tangent lifts.
Neither a generic tangent, a slope nor independent specialization points
are supplied as premises. -/
theorem actual_nilpotent_primitive_cone_forms_construct_normalized_tangent_lifts
    (H : Fin 4 → MvPolynomial (Fin 4) K) {d : ℕ} (hd : 0 < d) (hH : IsHomogMap H d)
    (hN : IsNilpotent (jac H)) (P : MvPolynomial (Fin 3) K)
    (A B : Fin 3 → Polynomial K) (hA : LinearIndependent K A)
    (hfirst : ∀ i : Fin 3, secondCoordinateAffineChart (H i.castSucc) = Polynomial.aeval P (A i))
    (hlast : secondCoordinateAffineChart (H (Fin.last 3)) = affineConeMixedPolynomial P B)
    (t : F) (ht : Transcendental K t) (x : Fin 3 → F) (hx : AlgebraicIndependent K x)
    (hvalue : t = aeval x P) (hclosed : algebraicClosure (IntermediateField.adjoin K {t}) F = ⊥)
    (hPw : pderiv (2 : Fin 3) P ≠ 0) :
    ∃ b₀ b₁ : Fin 3 → K, affineTangentLiftX b₀ P = 0 ∧ affineTangentLiftZ b₁ P = 0 := by
  let J := IntermediateField.adjoin K {t}
  let u : Fin 2 → J := fun i => Polynomial.aeval (IntermediateField.AdjoinSimple.gen K t)
    (coneTriangularHorizontalPolynomials d A i)
  let b : Fin 3 → J := fun i => Polynomial.aeval (IntermediateField.AdjoinSimple.gen K t)
    (coneTriangularVerticalPolynomials d A B i)
  have hu : LinearIndependent K u := actual_parameter_constructed_horizontal_polynomials_independent t ht hd A hA
  have hidentity := nilpotent_cone_affine_forms_construct_polynomial_tangent_identity H hH hN P A B hfirst hlast
  have hpoint := polynomial_parameter_tangent_identity_actual_source_value t x P hvalue
    (coneTriangularHorizontalPolynomials d A) (coneTriangularVerticalPolynomials d A B) hidentity
  have hc : (algebraMap (IntermediateField.adjoin K {t}) J).comp
      (algebraMap K (IntermediateField.adjoin K {t})) = algebraMap K J := by
    change (algebraMap J J).comp (algebraMap K J) = _
    rw [Algebra.algebraMap_self, RingHom.id_comp]
  have hglobal := actual_affine_level_tangent_forces_global_annihilation t ht x hx P hvalue hclosed
    (2 : Fin 3) hPw J F u b (by
      simpa only [hc, Algebra.algebraMap_self, RingHom.id_comp, RingHom.id_apply, u, b, J] using hpoint)
  have hglobal' : affineProjectedTangentAction u b (MvPolynomial.map (algebraMap K J) P) = 0 := by
    simpa only [hc] using hglobal
  exact independent_horizontal_coefficient_tangent_constructs_original_normalized_lifts P u hu b hglobal'

end DimensionFourDependence
