import DimensionFourDependence.GeometricPrimitiveAffineParameter
import DimensionFourDependence.AffineLevelGeometricIntegrality
import DimensionFourDependence.ConjugatedGaussAffineLevelTangent
import DimensionFourDependence.ActualGaussGenericTangentGraph
import DimensionFourDependence.ActualConeTangentConstruction

/-! # Geometrically integral affine level from the actual original cone data

The same actual primitive affine parameter retains the complete original
cone presentation and now supplies its full relation ideal and geometric
integrality. Tangency at its actual generic point also implies global
annihilation for every algebraic-parameter affine triangular tangent field.
No independent generic-level integrality hypothesis is added.
-/

namespace DimensionFourDependence

open MvPolynomial

attribute [local instance] MvPolynomial.gradedAlgebra

set_option quotPrecheck false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 100000

universe u

variable {K : Type u} [Field K] [CharZero K] [IsAlgClosed K]
    (H : Fin 4 → MvPolynomial (Fin 4) K)
    {d : ℕ} (hd : 0 < d) (hH : IsHomogMap H d)
    (hN : IsNilpotent (jac H)) (hrank : polyRank (jac H) = 3)
    (E : Type u) [Field E] [Algebra (polynomialOutputField H) E] [Algebra K E]
    [IsScalarTower K (polynomialOutputField H) E]
    [Algebra.IsAlgebraic (polynomialOutputField H) E] [IsAlgClosed E]
    (P : Ideal (MvPolynomial (Fin 4) E)) [P.IsPrime]
    (hP : P ∈ (extendCoefficientIdeal E (fiberVanishingIdeal
      (L := polynomialOutputField H) (rationalCoordinate (K := K) (n := 4)))).minimalPrimes)

local notation "S₀" => FractionRing (MvPolynomial (Fin 4) K)
local notation "G₀" => FractionRing (MvPolynomial (Fin 4) E ⧸ P)
local notation "z₀" => primeQuotientCoordinate P

include hd hH hN hrank hP

attribute [-instance] IntermediateField.instSMulSubtypeMem in
/-- The original geometric cone and fiber data construct an affine level
whose exact equation generates the whole relation ideal and remains
irreducible, with integral quotient, after every algebraic coefficient
extension of the actual parameter field. All previously constructed
original-source identities and the conditional tangent consequences remain. -/
theorem geometric_fixed_vertex_cone_constructs_geometrically_integral_affine_level
    (hind : ¬ ComponentsDependent H) (I : ImageRelationWitness H)
    (s : Equiv.Perm (Fin 4))
    (hY : AlgebraicIndependent K (fun i : Fin 3 => algebraMap (MvPolynomial (Fin 4) K) S₀ (H (s i.castSucc))))
    (h : coefficientField (K := K) (fun i : Fin 3 => algebraMap (MvPolynomial (Fin 4) K) S₀ (H (s i.castSucc))))
    (hh : (h : S₀) = algebraMap (MvPolynomial (Fin 4) K) S₀ (H (s 3)))
    (e : RatFunc K ≃ₐ[K] closedGaussParameterField H I)
    (hpara : LiesInAffineParabola (L := E) z₀) (hline : ¬ LiesInAffineLine (E := E) z₀)
    (p q : MvPolynomial (Fin 4) K) (hp : p ≠ 0) (hq : q ≠ 0) (hrel : IsRelPrime p q)
    {D : ℕ} (hpH : p.IsHomogeneous D) (hqH : q.IsHomogeneous D)
    (hparameter : closedGaussParameterSourceHom H I e RatFunc.X =
      algebraMap (MvPolynomial (Fin 4) K) S₀ p / algebraMap (MvPolynomial (Fin 4) K) S₀ q)
    (r₀ : MvPolynomial (Fin 4) K) (hr₀ : r₀ = p ∨ r₀ = q) (hrvertex : 0 < r₀.degreeOf (Fin.last 3)) :
    ∃ g : closedGaussParameterField H I →ₐ[K] E,
      CompatibleGeometricSourceRealization H I P g ∧
      ∀ (t : G₀), Transcendental E t → ∀ (x A : Fin 3 → E) (w0 B C : E),
      (∀ i : Fin 3, z₀ i.castSucc = algebraMap E G₀ (x i) + algebraMap E G₀ (A i) * t) →
      (z₀ (Fin.last 3) = algebraMap E G₀ w0 + algebraMap E G₀ B * t + algebraMap E G₀ C * t ^ 2) →
      ∀ (ν : Fin 3 → g.fieldRange) (k : Fin 3), ν k ≠ 0 →
      Algebra.trdeg K (projectiveRatioField (K := K) ν k) ≠ 0 →
      (∑ i : Fin 3, (ν i : E) * A i) = 0 → ∀ (j : Fin 3), A j = 1 →
      ∀ (R : E), R ≠ 0 → ∀ (κ : g.fieldRange), κ ≠ 0 → C = (κ : E) / R →
      ∀ (V : Fin 3 → E) (a b : E), (∀ i, IsAlgebraic g.fieldRange (V i)) →
      IsAlgebraic g.fieldRange a → IsAlgebraic g.fieldRange b →
      (∀ i : Fin 3, aeval z₀ (H i.castSucc) = algebraMap E G₀ (V i) * (algebraMap E G₀ R) ^ d) →
      (aeval z₀ (H (Fin.last 3)) = algebraMap E G₀ a * (algebraMap E G₀ R) ^ d +
        algebraMap E G₀ b * (algebraMap E G₀ R) ^ (d - 1) *
          (∑ i : Fin 3, algebraMap E G₀ (ν i : E) * z₀ i.castSucc)) →
    ∃ v : RatFunc K ≃ₐ[K] RatFunc K,
      (v = AlgEquiv.refl ∨ ∃ c : K, v = constantReciprocalParameterEquiv c) ∧
      ∃ (T S : Matrix (Fin 3) (Fin 3) K)
        (hTS : vertexPreservingMatrix T * vertexPreservingMatrix S = 1)
        (hST : vertexPreservingMatrix S * vertexPreservingMatrix T = 1)
        (τ : S₀),
        τ = matrixSourceFractionEquiv (vertexPreservingMatrix T) (vertexPreservingMatrix S) hTS hST
          (closedGaussParameterSourceHom H I (v.trans e) RatFunc.X) ∧
        Transcendental K τ ∧ algebraicClosure (IntermediateField.adjoin K {τ}) S₀ = ⊥ ∧
        linearPolynomialPullback (vertexPreservingMatrix T) (X (Fin.last 3)) = X (Fin.last 3) ∧
        IsHomogMap (linearPolynomialConjugate (vertexPreservingMatrix T) (vertexPreservingMatrix S) H) d ∧
        IsNilpotent (jac (linearPolynomialConjugate (vertexPreservingMatrix T) (vertexPreservingMatrix S) H)) ∧
        polyRank (jac (linearPolynomialConjugate (vertexPreservingMatrix T) (vertexPreservingMatrix S) H)) = 3 ∧
        ¬ ComponentsDependent (linearPolynomialConjugate (vertexPreservingMatrix T) (vertexPreservingMatrix S) H) ∧
        ∃ (a₀ b₀ : Fin 3 → Polynomial K) (P₀ : MvPolynomial (Fin 3) K),
          (∃ i, 0 < (a₀ i).natDegree) ∧ 0 < P₀.totalDegree ∧ P₀.totalDegree ≤ d ∧
          τ = aeval
            ![rationalCoordinate (K := K) (0 : Fin 4) / rationalCoordinate (K := K) (1 : Fin 4),
              rationalCoordinate (K := K) (2 : Fin 4) / rationalCoordinate (K := K) (1 : Fin 4),
              rationalCoordinate (K := K) (3 : Fin 4) / rationalCoordinate (K := K) (1 : Fin 4)] P₀ ∧
          (∀ i : Fin 3, algebraMap (MvPolynomial (Fin 4) K) S₀
            (linearPolynomialConjugate (vertexPreservingMatrix T) (vertexPreservingMatrix S) H i.castSucc) =
              Polynomial.aeval τ (a₀ i) * rationalCoordinate (K := K) (1 : Fin 4) ^ d) ∧
          algebraMap (MvPolynomial (Fin 4) K) S₀
            (linearPolynomialConjugate (vertexPreservingMatrix T) (vertexPreservingMatrix S) H (Fin.last 3)) =
              rationalCoordinate (K := K) (1 : Fin 4) ^ (d - 1) *
                ∑ i : Fin 3, Polynomial.aeval τ (b₀ i) * rationalCoordinate (K := K) i.castSucc ∧
          (∀ i : Fin 3, secondCoordinateAffineChart
            (linearPolynomialConjugate (vertexPreservingMatrix T) (vertexPreservingMatrix S) H i.castSucc) =
              Polynomial.aeval P₀ (a₀ i)) ∧
          secondCoordinateAffineChart
            (linearPolynomialConjugate (vertexPreservingMatrix T) (vertexPreservingMatrix S) H (Fin.last 3)) =
              Polynomial.aeval P₀ (b₀ 0) * X 0 + Polynomial.aeval P₀ (b₀ 1) +
                Polynomial.aeval P₀ (b₀ 2) * X 1 ∧
          affineConeTracePolynomial d P₀ a₀ b₀ = 0 ∧ (a₀ 1).derivative ≠ 0 ∧
          rationalPartial (K := K) (Fin.last 3) τ ≠ 0 ∧ pderiv (2 : Fin 3) P₀ ≠ 0 ∧
          Transcendental (IntermediateField.adjoin K (Set.range
            (![rationalCoordinate (K := K) (0 : Fin 4) / rationalCoordinate (K := K) (1 : Fin 4),
              rationalCoordinate (K := K) (2 : Fin 4) / rationalCoordinate (K := K) (1 : Fin 4)] : Fin 2 → S₀))) τ ∧
          fiberVanishingIdeal (L := IntermediateField.adjoin K {τ})
            ![rationalCoordinate (K := K) (0 : Fin 4) / rationalCoordinate (K := K) (1 : Fin 4),
              rationalCoordinate (K := K) (2 : Fin 4) / rationalCoordinate (K := K) (1 : Fin 4),
              rationalCoordinate (K := K) (3 : Fin 4) / rationalCoordinate (K := K) (1 : Fin 4)] = Ideal.span {actualAffineLevelEquation τ P₀} ∧
          (∀ (L : Type u) [Field L] [Algebra (IntermediateField.adjoin K {τ}) L]
            [Algebra.IsAlgebraic (IntermediateField.adjoin K {τ}) L],
            IsDomain (MvPolynomial (Fin 3) L ⧸ Ideal.span
              {MvPolynomial.map (algebraMap (IntermediateField.adjoin K {τ}) L)
                (actualAffineLevelEquation τ P₀)}) ∧
            Irreducible (MvPolynomial.map (algebraMap (IntermediateField.adjoin K {τ}) L)
              (actualAffineLevelEquation τ P₀))) ∧
          (∀ (L M : Type u) [Field L] [Field M]
            [Algebra (IntermediateField.adjoin K {τ}) L]
            [Algebra.IsAlgebraic (IntermediateField.adjoin K {τ}) L]
            [Algebra (IntermediateField.adjoin K {τ}) M] [Algebra S₀ M]
            [IsScalarTower (IntermediateField.adjoin K {τ}) S₀ M]
            [Algebra L M] [IsScalarTower (IntermediateField.adjoin K {τ}) L M]
            (u : Fin 2 → L) (β : Fin 3 → L),
            aeval (fun i => algebraMap S₀ M
              (closedGaussPencilChartPoint (K := K) (finSuccEquiv' (1 : Fin 4)) i))
              (affineProjectedTangentAction u β
                (MvPolynomial.map ((algebraMap (IntermediateField.adjoin K {τ}) L).comp
                  (algebraMap K (IntermediateField.adjoin K {τ}))) P₀)) = 0 →
            affineProjectedTangentAction u β
              (MvPolynomial.map ((algebraMap (IntermediateField.adjoin K {τ}) L).comp
                (algebraMap K (IntermediateField.adjoin K {τ}))) P₀) = 0) ∧
          (∀ (L M : Type u) [Field L] [Field M]
            [Algebra (IntermediateField.adjoin K {τ}) L] [Algebra K L]
            [IsScalarTower K (IntermediateField.adjoin K {τ}) L]
            [Algebra.IsAlgebraic (IntermediateField.adjoin K {τ}) L]
            [Algebra (IntermediateField.adjoin K {τ}) M] [Algebra S₀ M]
            [IsScalarTower (IntermediateField.adjoin K {τ}) S₀ M]
            [Algebra L M] [IsScalarTower (IntermediateField.adjoin K {τ}) L M]
            (u : Fin 2 → L), LinearIndependent K u → ∀ (β : Fin 3 → L),
            aeval (fun i => algebraMap S₀ M
              (closedGaussPencilChartPoint (K := K) (finSuccEquiv' (1 : Fin 4)) i))
              (affineProjectedTangentAction u β (MvPolynomial.map (algebraMap K L) P₀)) = 0 →
            ∃ Q : MvPolynomial (Fin 2) K, Q.totalDegree ≤ 2 ∧
              ∃ a b : K, a ≠ 0 ∧ P₀ = MvPolynomial.C a * (X 2 - rename Fin.castSucc Q) + MvPolynomial.C b) ∧
          (∃ β₀ β₁ : Fin 3 → K, affineTangentLiftX β₀ P₀ = 0 ∧ affineTangentLiftZ β₁ P₀ = 0) ∧
          (P₀.totalDegree = 1 ∧ ∃ Q : MvPolynomial (Fin 2) K, Q.totalDegree ≤ 1 ∧
            ∃ a b : K, a ≠ 0 ∧ P₀ = MvPolynomial.C a * (X 2 - rename Fin.castSucc Q) + MvPolynomial.C b) ∧
          (∀ (u₁ u₂ : Fin 2 → K), LinearIndependent K ![u₁, u₂] →
            ∀ (β₁ β₂ : Fin 3 → K), affineProjectedTangentAction u₁ β₁ P₀ = 0 →
              affineProjectedTangentAction u₂ β₂ P₀ = 0 →
              P₀.totalDegree = 1 ∧ ∃ Q : MvPolynomial (Fin 2) K, Q.totalDegree ≤ 1 ∧
                ∃ a b : K, a ≠ 0 ∧ P₀ = MvPolynomial.C a * (X 2 - rename Fin.castSucc Q) + MvPolynomial.C b) ∧
          (∀ (u₁ u₂ : Fin 2 → K), LinearIndependent K ![u₁, u₂] →
            ∀ (β₁ β₂ : Fin 3 → K), affineProjectedTangentAction u₁ β₁ P₀ = 0 →
              affineProjectedTangentAction u₂ β₂ P₀ = 0 →
              ∃ (Q : MvPolynomial (Fin 2) K) (F : Polynomial K), Q.totalDegree ≤ 2 ∧ 0 < F.natDegree ∧
                P₀ = Polynomial.aeval (X 2 - rename Fin.castSucc Q) F) ∧
          ∀ (a b : K) (Q : MvPolynomial (Fin 2) K), Q.totalDegree ≤ 2 →
            homogeneousComponent 2 Q ≠ 0 →
            P₀ ≠ MvPolynomial.C a * (X 2 - rename Fin.castSucc Q) + MvPolynomial.C b := by
  classical
  obtain ⟨g, hcompat, hg⟩ := geometric_fixed_vertex_cone_primitive_parameter_independent_tangents_force_affine_parameter
    H hd hH hN hrank E P hP hind I s hY h hh e hpara hline p q hp hq hrel hpH hqH hparameter r₀ hr₀ hrvertex
  refine ⟨g, hcompat, ?_⟩
  intro t ht x A w0 B C hx hw ν k hk hdim hinc j hj R hR κ hκ hC V a b hV ha hb hfirst hlast
  obtain ⟨v, hv, T, S, hTS, hST, τ, hτ, htrans, hclosed, hvertex, hhom, hnil, hrank', hind',
    a₀, b₀, P₀, hnonconstant, hPpositive, hPdegree, hPvalue, hfirst', hlast',
    hchartfirst, hchartlast, htrace, hderivative, hsourcepartial, hpolypartial, htransverse,
    hforced, hcomposite, hnoquadratic⟩ :=
    hg t ht x A w0 B C hx hw ν k hk hdim hinc j hj R hR κ hκ hC V a b hV ha hb hfirst hlast
  let ξ := closedGaussPencilChartPoint (K := K) (finSuccEquiv' (1 : Fin 4))
  have hξ : AlgebraicIndependent K ξ := algebraicIndependent_iff_injective_aeval.mpr
    (projective_source_chart_evaluation_injective _)
  have hchartvalue : τ = aeval ξ P₀ := by
    rw [show ξ = _ from second_coordinate_cone_chart_point]
    exact hPvalue
  have hrelation := actual_affine_level_parameter_field_relation_ideal τ htrans ξ hξ P₀ hchartvalue
  have hcurve := original_cone_common_scalar_values_polynomial_curve_independent
    (linearPolynomialConjugate (vertexPreservingMatrix T) (vertexPreservingMatrix S) H)
    hind' τ (rationalCoordinate (K := K) (1 : Fin 4)) d a₀ hfirst'
  obtain ⟨β₀, β₁, hβ₀, hβ₁⟩ :=
    actual_nilpotent_primitive_cone_forms_construct_normalized_tangent_lifts
      (linearPolynomialConjugate (vertexPreservingMatrix T) (vertexPreservingMatrix S) H)
      hd hhom hnil P₀ a₀ b₀ hcurve hchartfirst hchartlast τ htrans ξ hξ hchartvalue hclosed hpolypartial
  obtain ⟨Q₀, F₀, hQ₀, hF₀, hPF₀⟩ :=
    invariant_affine_tangent_lifts_construct_quadratic_composite_parameter P₀ hpolypartial β₀ β₁ hβ₀ hβ₁
  obtain ⟨_houter, a₁, b₁, ha₁, hshape₁⟩ :=
    actual_conjugate_gauss_affine_composite_parameter_constructs_affine_graph
      H I (v.trans e)
      (matrixSourceFractionEquiv (vertexPreservingMatrix T) (vertexPreservingMatrix S) hTS hST)
      τ hτ P₀ hchartvalue Q₀ F₀ hF₀ hPF₀
  have hQ₀₂ : homogeneousComponent 2 Q₀ = 0 := by
    by_contra hne
    exact hnoquadratic a₁ b₁ Q₀ hQ₀ hne hshape₁
  have hQ₀degree := quadratic_polynomial_zero_quadratic_part_degree_le_one Q₀ hQ₀ hQ₀₂
  have hPlinear : P₀.totalDegree ≤ 1 := by
    rw [hshape₁]
    apply (totalDegree_add _ _).trans
    refine max_le ?_ (by simp)
    apply (totalDegree_mul _ _).trans
    simp only [totalDegree_C, zero_add]
    apply (totalDegree_sub _ _).trans
    exact max_le (by simp) ((totalDegree_rename_le Fin.castSucc Q₀).trans hQ₀degree)
  have hPdegreeone : P₀.totalDegree = 1 := by omega
  refine ⟨v, hv, T, S, hTS, hST, τ, hτ, htrans, hclosed, hvertex, hhom, hnil, hrank', hind',
    a₀, b₀, P₀, hnonconstant, hPpositive, hPdegree, hPvalue, hfirst', hlast',
    hchartfirst, hchartlast, htrace, hderivative, hsourcepartial, hpolypartial, htransverse,
    ?_, ?_, ?_, ?_, ⟨β₀, β₁, hβ₀, hβ₁⟩,
    ⟨hPdegreeone, Q₀, hQ₀degree, a₁, b₁, ha₁, hshape₁⟩, hforced, hcomposite, hnoquadratic⟩
  · rw [← second_coordinate_cone_chart_point]
    exact hrelation
  · intro L _ _ _
    exact ⟨actual_affine_level_geometrically_integral τ htrans ξ hξ P₀ hchartvalue hclosed L,
      actual_affine_level_geometrically_irreducible τ htrans ξ hξ P₀ hchartvalue hclosed
        (2 : Fin 3) hpolypartial L⟩
  · intro L M _ _ _ _ _ _ _ _ _ u β htan
    exact actual_conjugate_gauss_affine_level_tangent_forces_global_annihilation
      H I (v.trans e)
      (matrixSourceFractionEquiv (vertexPreservingMatrix T) (vertexPreservingMatrix S) hTS hST)
      τ hτ P₀ hchartvalue (2 : Fin 3) hpolypartial L M u β htan
  · intro L M _ _ _ _ _ _ _ _ _ _ _ u hu β htan
    exact actual_conjugate_gauss_generic_tangent_constructs_original_quadratic_graph_parameter
      H I (v.trans e)
      (matrixSourceFractionEquiv (vertexPreservingMatrix T) (vertexPreservingMatrix S) hTS hST)
      τ hτ P₀ hchartvalue hpolypartial L M u hu β htan

end DimensionFourDependence
