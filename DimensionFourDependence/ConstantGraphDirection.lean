import DimensionFourDependence.CoefficientIsotropicLine

/-! # A constant tangent direction lowers the graph Hessian rank

A weight-one three-variable graph has its radial direction in the Hessian
kernel. A nonzero constant tangent direction gives a second independent
kernel vector, so the Hessian has rank at most one. This is the algebraic
Gauss-dimension obstruction for the concurrent-line (cone) case.
-/

namespace DimensionFourDependence

open Matrix Module

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

/-- Independent coordinate values and a nonzero constant vector cannot be
proportional over the extension field. -/
theorem independent_coordinates_constant_vector_pair
    (Y : Fin 3 → F) (hY : LinearIndependent K Y) (a : Fin 3 → K) (ha : a ≠ 0) :
    LinearIndependent F ![Y, (fun i => algebraMap K F (a i))] := by
  rw [linearIndependent_fin2]
  constructor
  · change (fun i => algebraMap K F (a i)) ≠ 0
    intro hz
    apply ha
    funext i
    apply (algebraMap K F).injective
    simpa only [map_zero, Pi.zero_apply] using congrFun hz i
  · intro s he
    change s • (fun i => algebraMap K F (a i)) = Y at he
    obtain ⟨i, hi⟩ : ∃ i, a i ≠ 0 := by
      simpa only [ne_eq, funext_iff, Pi.zero_apply, not_forall] using ha
    obtain ⟨j, hji⟩ : ∃ j : Fin 3, j ≠ i := exists_ne i
    have hinj : Function.Injective (![i, j] : Fin 2 → Fin 3) := by
      intro k l hkl
      fin_cases k <;> fin_cases l <;> simp_all
    have hpair : LinearIndependent K ![Y i, Y j] := by
      have heq : Y ∘ (![i, j] : Fin 2 → Fin 3) = ![Y i, Y j] := by
        funext k
        fin_cases k <;> rfl
      rw [← heq]
      exact hY.comp ![i, j] hinj
    have hrel : a j • Y i = a i • Y j := by
      rw [← congrFun he i, ← congrFun he j]
      simp only [Pi.smul_apply, Algebra.smul_def]
      ring
    exact hi (hpair.eq_zero_of_pair' hrel).2

/-- Two independent kernel vectors bound a three-by-three matrix's rank by one. -/
theorem matrix_three_rank_le_one_of_independent_kernel_pair
    (T : Matrix (Fin 3) (Fin 3) F) (u v : Fin 3 → F)
    (hli : LinearIndependent F ![u, v]) (hu : T *ᵥ u = 0) (hv : T *ᵥ v = 0) :
    T.rank ≤ 1 := by
  have hle : Submodule.span F (Set.range ![u, v]) ≤ LinearMap.ker T.toLin' := by
    apply Submodule.span_le.mpr
    rintro _ ⟨i, rfl⟩
    fin_cases i
    · exact hu
    · exact hv
  have hdim : finrank F (Submodule.span F (Set.range ![u, v])) = 2 := by
    simpa using finrank_span_eq_card hli
  have hbound := Submodule.finrank_mono hle
  have hsum := LinearMap.finrank_range_add_finrank_ker T.toLin'
  have hr : finrank F (LinearMap.range T.toLin') = T.rank := rfl
  simp only [Module.finrank_pi, Fintype.card_fin] at hsum
  omega

variable [CharZero K]

omit [Field F] [Algebra K F] in
/-- A constant affine-linear relation among graph-gradient coordinates
gives a constant vector in the actual coefficient Hessian kernel. -/
theorem coefficientHessian_constant_tangent_kernel
    (Y : Fin 3 → FractionRing (MvPolynomial (Fin 4) K)) (hY : AlgebraicIndependent K Y)
    (h : coefficientField (K := K) Y) (a : Fin 3 → K) (b : K)
    (htangent : (∑ j, algebraMap K (coefficientField (K := K) Y) (a j) *
      coefficientGradient Y hY h j) = algebraMap K (coefficientField (K := K) Y) b) :
    coefficientHessian Y hY h *ᵥ (fun j => algebraMap K (coefficientField (K := K) Y) (a j)) = 0 := by
  funext i
  have he := congrArg (coefficientPartial (K := K) Y hY i) htangent
  have he0 : (∑ j, algebraMap K (coefficientField (K := K) Y) (a j) *
      coefficientHessian Y hY h i j) = 0 := by
    simpa only [map_sum, Derivation.leibniz, Derivation.map_algebraMap,
      mul_zero, add_zero, smul_eq_mul, coefficientGradient, coefficientHessian,
      Matrix.of_apply] using he
  change (∑ j, coefficientHessian Y hY h i j *
    algebraMap K (coefficientField (K := K) Y) (a j)) = 0
  calc
    _ = ∑ j, algebraMap K (coefficientField (K := K) Y) (a j) *
        coefficientHessian Y hY h i j := by
      apply Finset.sum_congr rfl
      intro j _
      exact mul_comm _ _
    _ = 0 := he0

omit [Field F] [Algebra K F] in
/-- A nonzero constant tangent direction on a weight-one graph forces
rank at most one for its actual coefficient Hessian. -/
theorem coefficientHessian_rank_le_one_of_constant_tangent
    (Y : Fin 3 → FractionRing (MvPolynomial (Fin 4) K)) (hY : AlgebraicIndependent K Y)
    (h : coefficientField (K := K) Y) (hEuler : coefficientEuler Y hY h = h)
    (a : Fin 3 → K) (ha : a ≠ 0) (b : K)
    (htangent : (∑ j, algebraMap K (coefficientField (K := K) Y) (a j) *
      coefficientGradient Y hY h j) = algebraMap K (coefficientField (K := K) Y) b) :
    (coefficientHessian Y hY h).rank ≤ 1 := by
  let : IsScalarTower K (coefficientField (K := K) Y)
    (FractionRing (MvPolynomial (Fin 4) K)) := coefficientFieldScalarTower Y
  have hcoord : LinearIndependent K (coefficientCoordinate (K := K) Y) := by
    apply LinearIndependent.of_comp (IsScalarTower.toAlgHom K (coefficientField (K := K) Y)
      (FractionRing (MvPolynomial (Fin 4) K))).toLinearMap
    have heq : (IsScalarTower.toAlgHom K (coefficientField (K := K) Y)
        (FractionRing (MvPolynomial (Fin 4) K))).toLinearMap ∘
          coefficientCoordinate (K := K) Y = Y := by
      funext i
      change (coefficientCoordinate (K := K) Y i : FractionRing (MvPolynomial (Fin 4) K)) = Y i
      rfl
    rw [heq]
    exact hY.linearIndependent
  have hli := independent_coordinates_constant_vector_pair
    (coefficientCoordinate (K := K) Y) hcoord a ha
  exact matrix_three_rank_le_one_of_independent_kernel_pair (coefficientHessian Y hY h)
    (coefficientCoordinate (K := K) Y) _ hli
    (by simpa using coefficientHessian_radial_mulVec_map Y hY (coefficientField (K := K) Y) h hEuler)
    (coefficientHessian_constant_tangent_kernel Y hY h a b htangent)

end DimensionFourDependence
