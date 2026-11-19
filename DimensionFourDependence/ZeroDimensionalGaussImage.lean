import DimensionFourDependence.GaussImageBound
import DimensionFourDependence.AlgebraicNormalRatios

/-! # A zero-dimensional actual Gauss image forces a plane

The ratio-field argument over algebraically closed coefficients is
checked separately. For the original characteristic-zero field, algebraic
normal ratios give polynomial Wronskian identities and constant homogeneous
proportionality. Euler's identity then gives the actual component relation.
-/

namespace DimensionFourDependence

open MvPolynomial Matrix

variable {K F : Type*} [Field K] [IsAlgClosed K] [Field F] [Algebra K F]

/-- A projective coordinate vector with zero-dimensional ratio field
is a nonzero scalar multiple of an actual constant vector. -/
theorem projective_ratio_trdeg_zero_constant_vector
    (ν : Fin 4 → F) (a : Fin 4) (ha : ν a ≠ 0)
    (hzero : Algebra.trdeg K (projectiveRatioField (K := K) ν a) = 0) :
    ∃ c : Fin 4 → K, c ≠ 0 ∧ ∀ i, ν i = ν a * algebraMap K F (c i) := by
  let L := projectiveRatioField (K := K) ν a
  let : Algebra.IsAlgebraic K L := trdeg_eq_zero_iff.mp hzero
  have hL : L = ⊥ := L.eq_bot_of_isAlgClosed_of_isAlgebraic
  have hscalar (i : Fin 4) : ∃ c : K, algebraMap K F c = ν i / ν a := by
    have hm : ν i / ν a ∈ L := IntermediateField.subset_adjoin K _ ⟨i, rfl⟩
    rw [hL, IntermediateField.mem_bot] at hm
    exact hm
  choose c hc using hscalar
  refine ⟨c, ?_, ?_⟩
  · intro hz
    have he := hc a
    rw [congrFun hz a, Pi.zero_apply, map_zero, div_self ha] at he
    exact zero_ne_one he
  · intro i
    rw [hc, mul_div_cancel₀ _ ha]

variable [CharZero K]

omit [Field F] [Algebra K F] [IsAlgClosed K] in
/-- A zero-dimensional actual Gauss image gives a constant component
relation over the original characteristic-zero coefficient field. -/
theorem componentsDependent_of_gauss_image_dimension_zero
    (H : Fin 4 → MvPolynomial (Fin 4) K) {d : ℕ} (hd : 0 < d) (hH : IsHomogMap H d)
    (I : ImageRelationWitness H) (hzero : gaussImageDimension H I = 0) :
    ComponentsDependent H := by
  obtain ⟨c, hc, hν⟩ := I.normal_constant_vector_of_gauss_image_dimension_zero H hH hzero
  refine ⟨c, hc, ?_⟩
  let f := imageRelationNormal H I.equation (imageNormalPivot H I)
  have hf : f ≠ 0 := by
    intro hz
    apply imageNormalPivot_ne_zero H I
    change algebraMap (MvPolynomial (Fin 4) K) (FractionRing (MvPolynomial (Fin 4) K)) f = 0
    rw [hz, map_zero]
  have hpol := left_normal_dot_eq_zero H (imageRelationNormal H I.equation) hd.ne' hH (I.left_kernel H)
  have hscaled : f * (∑ i, c i • H i) = 0 := by
    calc
      _ = ∑ i, (c i • f) * H i := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i _
        simp only [MvPolynomial.smul_eq_C_mul]
        ring
      _ = ∑ i, imageRelationNormal H I.equation i * H i := by
        apply Finset.sum_congr rfl
        intro i _
        exact congrArg (fun z => z * H i) (hν i).symm
      _ = 0 := hpol
  exact (mul_eq_zero.mp hscaled).resolve_left hf

omit [Field F] [Algebra K F] [IsAlgClosed K] in
/-- At rank three, zero Gauss dimension means that the actual defining
equation is linear, hence the actual image hypersurface is a plane. -/
theorem ImageRelationWitness.degree_one_of_gauss_image_dimension_zero
    (H : Fin 4 → MvPolynomial (Fin 4) K) {d : ℕ} (hd : 0 < d) (hH : IsHomogMap H d)
    (hrank : polyRank (jac H) = 3) (I : ImageRelationWitness H)
    (hzero : gaussImageDimension H I = 0) : I.degree = 1 :=
  I.degree_one_of_dependent H hrank (componentsDependent_of_gauss_image_dimension_zero H hd hH I hzero)

end DimensionFourDependence
