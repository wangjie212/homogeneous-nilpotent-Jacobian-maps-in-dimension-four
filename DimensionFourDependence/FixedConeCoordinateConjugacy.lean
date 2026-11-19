import DimensionFourDependence.FixedCovectorCoordinateChoice

/-! # The complete cone forms under actual source and target conjugacy

The constant coordinate matrices constructed from the fixed covector
transport the original source-field parameter and all four original
coordinate values. The first three scalar polynomials and the fourth
linear quotient remain polynomial after the target and source changes.
-/

namespace DimensionFourDependence

open MvPolynomial Matrix

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 100000

variable {K : Type*} [Field K]

local notation "R₀" => MvPolynomial (Fin 4) K
local notation "S₀" => FractionRing (MvPolynomial (Fin 4) K)

/-- The source value of every conjugated coordinate is the inverse
constant target combination of the transported original values. -/
theorem linearPolynomialConjugate_source_value
    {n : ℕ} (T S : Matrix (Fin n) (Fin n) K) (hTS : T * S = 1) (hST : S * T = 1)
    (H : Fin n → MvPolynomial (Fin n) K) (i : Fin n) :
    algebraMap (MvPolynomial (Fin n) K) (FractionRing (MvPolynomial (Fin n) K))
      (linearPolynomialConjugate T S H i) =
      ∑ k, algebraMap K (FractionRing (MvPolynomial (Fin n) K)) (S i k) *
        matrixSourceFractionEquiv T S hTS hST
          (algebraMap (MvPolynomial (Fin n) K) (FractionRing (MvPolynomial (Fin n) K)) (H k)) := by
  simp only [linearPolynomialConjugate, map_sum, map_mul,
    matrixSourceFractionEquiv_polynomial, ← MvPolynomial.algebraMap_eq,
    ← IsScalarTower.algebraMap_apply K (MvPolynomial (Fin n) K) (FractionRing (MvPolynomial (Fin n) K))]

/-- The full source-field automorphism sends each original rational
coordinate to the same original constant linear combination as the
polynomial coordinate substitution. -/
theorem matrixSourceFractionEquiv_coordinate
    {n : ℕ} (T S : Matrix (Fin n) (Fin n) K) (hTS : T * S = 1) (hST : S * T = 1)
    (i : Fin n) :
    matrixSourceFractionEquiv T S hTS hST (rationalCoordinate (K := K) i) =
      ∑ k, algebraMap K (FractionRing (MvPolynomial (Fin n) K)) (T i k) *
        rationalCoordinate (K := K) k := by
  rw [rationalCoordinate, matrixSourceFractionEquiv_polynomial]
  simp only [linearPolynomialPullback, aeval_X, linearPolynomialMap, map_sum, map_mul,
    ← MvPolynomial.algebraMap_eq,
    ← IsScalarTower.algebraMap_apply K (MvPolynomial (Fin n) K) (FractionRing (MvPolynomial (Fin n) K)),
    rationalCoordinate]

/-- Complete fixed cone source formulas remain polynomial in the
transported actual source parameter after a vertex-preserving conjugacy. -/
theorem complete_fixed_cone_source_forms_transport_under_conjugacy
    (H : Fin 4 → R₀) (d : ℕ) (t : S₀) (c : Fin 3 → K)
    (A B : Fin 3 → Polynomial K)
    (hfirst : ∀ i : Fin 3, algebraMap R₀ S₀ (H i.castSucc) =
      Polynomial.aeval t (A i) * (algebraMap R₀ S₀ (rename Fin.castSucc (linearFormPolynomial c))) ^ d)
    (hlast : algebraMap R₀ S₀ (H (Fin.last 3)) =
      (algebraMap R₀ S₀ (rename Fin.castSucc (linearFormPolynomial c))) ^ (d - 1) *
        ∑ i : Fin 3, Polynomial.aeval t (B i) * rationalCoordinate (K := K) i.castSucc)
    (T S : Matrix (Fin 3) (Fin 3) K)
    (hTS : vertexPreservingMatrix T * vertexPreservingMatrix S = 1)
    (hST : vertexPreservingMatrix S * vertexPreservingMatrix T = 1)
    (j : Fin 3)
    (hlinear : linearPolynomialPullback (vertexPreservingMatrix T)
      (rename Fin.castSucc (linearFormPolynomial c)) = X j.castSucc) :
    ∃ A' B' : Fin 3 → Polynomial K,
      (∀ i : Fin 3, algebraMap R₀ S₀
        (linearPolynomialConjugate (vertexPreservingMatrix T) (vertexPreservingMatrix S) H i.castSucc) =
          Polynomial.aeval (matrixSourceFractionEquiv
            (vertexPreservingMatrix T) (vertexPreservingMatrix S) hTS hST t) (A' i) *
              rationalCoordinate (K := K) j.castSucc ^ d) ∧
      algebraMap R₀ S₀
        (linearPolynomialConjugate (vertexPreservingMatrix T) (vertexPreservingMatrix S) H (Fin.last 3)) =
          rationalCoordinate (K := K) j.castSucc ^ (d - 1) *
            ∑ i : Fin 3, Polynomial.aeval (matrixSourceFractionEquiv
              (vertexPreservingMatrix T) (vertexPreservingMatrix S) hTS hST t) (B' i) *
                rationalCoordinate (K := K) i.castSucc := by
  classical
  have hlastCases (a : K) (g : Fin 3 → K) : Fin.lastCases a g (3 : Fin 4) = a := by
    change Fin.lastCases a g (Fin.last 3) = a
    rw [Fin.lastCases_last]
  let f := matrixSourceFractionEquiv (vertexPreservingMatrix T) (vertexPreservingMatrix S) hTS hST
  let A' : Fin 3 → Polynomial K := fun i => ∑ k, Polynomial.C (S i k) * A k
  let B' : Fin 3 → Polynomial K := fun k => ∑ i, Polynomial.C (T i k) * B i
  have hy : f (algebraMap R₀ S₀ (rename Fin.castSucc (linearFormPolynomial c))) =
      rationalCoordinate (K := K) j.castSucc := by
    rw [matrixSourceFractionEquiv_polynomial, hlinear]
    rfl
  have hx (i : Fin 3) : f (rationalCoordinate (K := K) i.castSucc) =
      ∑ k : Fin 3, algebraMap K S₀ (T i k) * rationalCoordinate (K := K) k.castSucc := by
    rw [matrixSourceFractionEquiv_coordinate, Fin.sum_univ_castSucc]
    simp [vertexPreservingMatrix, hlastCases]
  have hfirstmap (i : Fin 3) : algebraMap R₀ S₀
      (linearPolynomialConjugate (vertexPreservingMatrix T) (vertexPreservingMatrix S) H i.castSucc) =
        ∑ k : Fin 3, algebraMap K S₀ (S i k) * f (algebraMap R₀ S₀ (H k.castSucc)) := by
    rw [linearPolynomialConjugate_source_value _ _ hTS hST, Fin.sum_univ_castSucc]
    simp [vertexPreservingMatrix, f, hlastCases]
  have hlastmap : algebraMap R₀ S₀
      (linearPolynomialConjugate (vertexPreservingMatrix T) (vertexPreservingMatrix S) H (Fin.last 3)) =
        f (algebraMap R₀ S₀ (H (Fin.last 3))) := by
    rw [linearPolynomialConjugate_source_value _ _ hTS hST, Fin.sum_univ_castSucc]
    simp [vertexPreservingMatrix, f, hlastCases]
  refine ⟨A', B', ?_, ?_⟩
  · intro i
    rw [hfirstmap]
    simp_rw [hfirst, map_mul, map_pow, hy, ← Polynomial.aeval_algHom_apply f]
    simp only [A', map_sum, map_mul, Polynomial.aeval_C, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro k _
    ring
  · rw [hlastmap, hlast, map_mul, map_pow, hy, map_sum]
    simp_rw [map_mul, ← Polynomial.aeval_algHom_apply f, hx]
    apply congrArg (fun z => rationalCoordinate (K := K) j.castSucc ^ (d - 1) * z)
    simp only [B', map_sum, map_mul, Polynomial.aeval_C, Finset.mul_sum, Finset.sum_mul]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro k _
    apply Finset.sum_congr rfl
    intro i _
    ring

/-- The original complete fixed cone presentation constructs a genuine
coordinate conjugate satisfying (4.10) with the chosen coordinate y.
Homogeneity, nilpotence and component independence of the actual original
map are preserved, and some new scalar polynomial remains nonconstant. -/
theorem fixed_cone_forms_construct_coordinate_conjugate
    (H : Fin 4 → R₀) {d : ℕ} (hH : IsHomogMap H d)
    (hN : IsNilpotent (jac H)) (hind : ¬ ComponentsDependent H)
    (t : S₀) (c : Fin 3 → K) (hc : c ≠ 0) (A B : Fin 3 → Polynomial K)
    (hfirst : ∀ i : Fin 3, algebraMap R₀ S₀ (H i.castSucc) =
      Polynomial.aeval t (A i) * (algebraMap R₀ S₀ (rename Fin.castSucc (linearFormPolynomial c))) ^ d)
    (hlast : algebraMap R₀ S₀ (H (Fin.last 3)) =
      (algebraMap R₀ S₀ (rename Fin.castSucc (linearFormPolynomial c))) ^ (d - 1) *
        ∑ i : Fin 3, Polynomial.aeval t (B i) * rationalCoordinate (K := K) i.castSucc)
    (j : Fin 3) :
    ∃ (T S : Matrix (Fin 3) (Fin 3) K)
      (hTS : vertexPreservingMatrix T * vertexPreservingMatrix S = 1)
      (hST : vertexPreservingMatrix S * vertexPreservingMatrix T = 1),
      linearPolynomialPullback (vertexPreservingMatrix T)
        (rename Fin.castSucc (linearFormPolynomial c)) = X j.castSucc ∧
      linearPolynomialPullback (vertexPreservingMatrix T) (X (Fin.last 3)) = X (Fin.last 3) ∧
      IsHomogMap (linearPolynomialConjugate (vertexPreservingMatrix T) (vertexPreservingMatrix S) H) d ∧
      IsNilpotent (jac (linearPolynomialConjugate (vertexPreservingMatrix T) (vertexPreservingMatrix S) H)) ∧
      ¬ ComponentsDependent (linearPolynomialConjugate (vertexPreservingMatrix T) (vertexPreservingMatrix S) H) ∧
      ∃ A' B' : Fin 3 → Polynomial K, (∃ i, 0 < (A' i).natDegree) ∧
        (∀ i : Fin 3, algebraMap R₀ S₀
          (linearPolynomialConjugate (vertexPreservingMatrix T) (vertexPreservingMatrix S) H i.castSucc) =
            Polynomial.aeval (matrixSourceFractionEquiv
              (vertexPreservingMatrix T) (vertexPreservingMatrix S) hTS hST t) (A' i) *
                rationalCoordinate (K := K) j.castSucc ^ d) ∧
        algebraMap R₀ S₀
          (linearPolynomialConjugate (vertexPreservingMatrix T) (vertexPreservingMatrix S) H (Fin.last 3)) =
            rationalCoordinate (K := K) j.castSucc ^ (d - 1) *
              ∑ i : Fin 3, Polynomial.aeval (matrixSourceFractionEquiv
                (vertexPreservingMatrix T) (vertexPreservingMatrix S) hTS hST t) (B' i) *
                  rationalCoordinate (K := K) i.castSucc := by
  obtain ⟨T, S, hTS, hST, hlinear, hvertex⟩ :=
    fixed_covector_constructs_vertex_preserving_source_coordinates c hc j
  have hhom := linearPolynomialConjugate_homogeneous (vertexPreservingMatrix T) (vertexPreservingMatrix S) H hH
  have hnil := linearPolynomialConjugate_nilpotent (vertexPreservingMatrix T) (vertexPreservingMatrix S) hTS hST H hN
  have hind' := linearPolynomialConjugate_componentsIndependent
    (vertexPreservingMatrix T) (vertexPreservingMatrix S) hTS hST H hind
  obtain ⟨A', B', hfirst', hlast'⟩ := complete_fixed_cone_source_forms_transport_under_conjugacy
    H d t c A B hfirst hlast T S hTS hST j hlinear
  have hnonconstant := independent_original_outputs_polynomial_scalar_nonconstant
    (linearPolynomialConjugate (vertexPreservingMatrix T) (vertexPreservingMatrix S) H) hind'
    (matrixSourceFractionEquiv (vertexPreservingMatrix T) (vertexPreservingMatrix S) hTS hST t)
    (rationalCoordinate (K := K) j.castSucc) d A' hfirst'
  exact ⟨T, S, hTS, hST, hlinear, hvertex, hhom, hnil, hind', A', B', hnonconstant, hfirst', hlast'⟩

end DimensionFourDependence
