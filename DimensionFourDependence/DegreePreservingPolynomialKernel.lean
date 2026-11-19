import DimensionFourDependence.VertexLinePrime

/-! # Homogeneous components and degree-preserving polynomial kernels -/

namespace DimensionFourDependence

open MvPolynomial

attribute [local instance] MvPolynomial.gradedAlgebra

variable {K σ τ : Type*} [Field K]

/-- A degree-preserving polynomial homomorphism preserves each
individual homogeneous component, by uniqueness of the finite decomposition. -/
theorem degree_preserving_polynomial_hom_component
    (f : MvPolynomial σ K →ₐ[K] MvPolynomial τ K)
    (hf : ∀ (P : MvPolynomial σ K) (d : ℕ), P.IsHomogeneous d → (f P).IsHomogeneous d)
    (P : MvPolynomial σ K) (n : ℕ) :
    homogeneousComponent n (f P) = f (homogeneousComponent n P) := by
  classical
  have he : homogeneousComponent n (f P) =
      ∑ i ∈ Finset.range (P.totalDegree + 1),
        if n = i then f (homogeneousComponent i P) else 0 := by
    conv_lhs => rw [← sum_homogeneousComponent P]
    simp only [map_sum]
    apply Finset.sum_congr rfl
    intro i hi
    exact homogeneousComponent_of_mem (hf _ i (homogeneousComponent_isHomogeneous i P))
  rw [he]
  by_cases hn : n ∈ Finset.range (P.totalDegree + 1)
  · simp [hn]
  · have hn' : P.totalDegree < n := by
      have hle : P.totalDegree + 1 ≤ n := by simpa only [Finset.mem_range, not_lt] using hn
      omega
    simp [hn, homogeneousComponent_eq_zero n P hn']

/-- The exact kernel of a degree-preserving polynomial homomorphism
is a homogeneous ideal in the original source coordinates. -/
theorem degree_preserving_polynomial_hom_kernel_isHomogeneous
    (f : MvPolynomial σ K →ₐ[K] MvPolynomial τ K)
    (hf : ∀ (P : MvPolynomial σ K) (d : ℕ), P.IsHomogeneous d → (f P).IsHomogeneous d) :
    (RingHom.ker f.toRingHom).IsHomogeneous (homogeneousSubmodule σ K) := by
  intro d P hP
  change f (MvPolynomial.decomposition.decompose' P d) = 0
  rw [MvPolynomial.decomposition.decompose'_apply,
    ← degree_preserving_polynomial_hom_component f hf]
  change f P = 0 at hP
  rw [hP, map_zero]

/-- The actual vertex-line parametrization preserves every
homogeneous degree. -/
theorem vertexLineParameterHom_preserves_homogeneous_degree
    (b : Fin 3 → K) (j : Fin 3) (P : MvPolynomial (Fin 4) K) (d : ℕ)
    (hP : P.IsHomogeneous d) : (vertexLineParameterHom b j P).IsHomogeneous d := by
  unfold vertexLineParameterHom
  have hg : ∀ ℓ : Fin 4, ((Fin.snoc
      (fun i : Fin 3 => C (b i / b j) * X (0 : Fin 2)) (X (1 : Fin 2)) :
        Fin 4 → MvPolynomial (Fin 2) K) ℓ).IsHomogeneous 1 := by
    intro ℓ
    refine Fin.lastCases ?_ (fun i => ?_) ℓ
    · simpa only [Fin.snoc_last] using isHomogeneous_X (R := K) (1 : Fin 2)
    · simpa only [Fin.snoc_castSucc] using
        isHomogeneous_C_mul_X (b i / b j) (0 : Fin 2)
  simpa only [one_mul] using hP.aeval _ hg

/-- The exact original vertex-line prime is homogeneous. -/
theorem vertexLinePrime_isHomogeneous (b : Fin 3 → K) (j : Fin 3) :
    (vertexLinePrime b j).IsHomogeneous (homogeneousSubmodule (Fin 4) K) :=
  degree_preserving_polynomial_hom_kernel_isHomogeneous _
    (vertexLineParameterHom_preserves_homogeneous_degree b j)

end DimensionFourDependence
