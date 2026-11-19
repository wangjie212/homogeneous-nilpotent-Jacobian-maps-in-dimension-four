import DimensionFourDependence.VertexLinePrime
import DimensionFourDependence.NormalPlaneConstantIntersection

/-! # The vertex is on the line but the moving normal plane does not contain it

Exact kernel evaluation proves vertex incidence. Independent normal jets
exclude every nonzero transverse constant relation, hence exclude any
whole vertex line from the generic normal plane.
-/

namespace DimensionFourDependence

open MvPolynomial Matrix

set_option maxHeartbeats 2500000

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

/-- Every polynomial in the exact line prime vanishes at every
point of its two-coordinate parametrization, after any field extension. -/
theorem vertexLinePrime_parametric_point_evaluation_zero
    (b : Fin 3 → K) (j : Fin 3) (u v : F)
    (P : MvPolynomial (Fin 4) K) (hP : P ∈ vertexLinePrime b j) :
    aeval (Fin.snoc (fun i : Fin 3 => algebraMap K F (b i / b j) * u) v) P = 0 := by
  let φ : MvPolynomial (Fin 2) K →ₐ[K] F := aeval ![u, v]
  have he : φ.comp (vertexLineParameterHom b j) =
      aeval (Fin.snoc (fun i : Fin 3 => algebraMap K F (b i / b j) * u) v) := by
    apply MvPolynomial.algHom_ext
    intro ℓ
    refine Fin.lastCases ?_ (fun i => ?_) ℓ
    · simp only [AlgHom.comp_apply, vertexLineParameterHom, aeval_X, Fin.snoc_last]
      simp [φ]
    · simp [vertexLineParameterHom, φ]
  change vertexLineParameterHom b j P = 0 at hP
  rw [← he]
  change φ (vertexLineParameterHom b j P) = 0
  rw [hP, map_zero]

/-- The entire fourth axis, including the projective vertex, is
in the zero locus of the actual line prime over every coefficient field. -/
theorem vertexLinePrime_axis_evaluation_zero
    (b : Fin 3 → K) (j : Fin 3) (v : F)
    (P : MvPolynomial (Fin 4) K) (hP : P ∈ vertexLinePrime b j) :
    aeval (Fin.snoc (0 : Fin 3 → F) v) P = 0 := by
  have he := vertexLinePrime_parametric_point_evaluation_zero b j (0 : F) v P hP
  have hc : (fun i : Fin 3 => algebraMap K F (b i / b j) * (0 : F)) = 0 := by
    funext i
    exact mul_zero _
  rwa [hc] at he

/-- The specified transverse direction is a point of the exact
line prime, with its original coordinate labels preserved. -/
theorem vertexLinePrime_direction_evaluation_zero
    (b : Fin 3 → K) (j : Fin 3) (hj : b j ≠ 0)
    (P : MvPolynomial (Fin 4) K) (hP : P ∈ vertexLinePrime b j) :
    aeval (Fin.snoc (fun i : Fin 3 => algebraMap K F (b i)) 0) P = 0 := by
  have he := vertexLinePrime_parametric_point_evaluation_zero
    b j (algebraMap K F (b j)) 0 P hP
  have hc : (fun i : Fin 3 => algebraMap K F (b i / b j) * algebraMap K F (b j)) =
      (fun i => algebraMap K F (b i)) := by
    funext i
    rw [← map_mul, div_mul_cancel₀ _ hj]
  rwa [hc] at he

/-- A linear form pairing nontrivially with the direction cannot
vanish identically on the actual line. -/
theorem vertexLinePrime_linearForm_not_mem
    (b : Fin 3 → K) (j : Fin 3) (hj : b j ≠ 0) (w : Fin 4 → K)
    (hpair : (∑ i : Fin 3, w i.castSucc * b i) ≠ 0) :
    linearFormPolynomial w ∉ vertexLinePrime b j := by
  intro hmem
  have he := vertexLinePrime_direction_evaluation_zero (F := K) b j hj _ hmem
  apply hpair
  simp only [linearFormPolynomial, map_sum, map_mul, aeval_C, aeval_X,
    Algebra.algebraMap_self, RingHom.id_apply] at he
  rw [Fin.sum_univ_castSucc] at he
  simpa only [Fin.snoc_castSucc, Fin.snoc_last, mul_zero, add_zero] using he

/-- Three independent normal jets whose fourth coordinate is zero
annihilate no nonzero original transverse constant direction. -/
theorem independent_normal_jets_transverse_constant_pairing_ne_zero
    (D : Derivation K F F) (w : Fin 4 → F)
    (hLI : LinearIndependent F (normalCharacteristicMatrix D w).row)
    (hvertex : w (Fin.last 3) = 0)
    (b : Fin 3 → K) (hb : b ≠ 0) :
    (∑ i : Fin 3, w i.castSucc * algebraMap K F (b i)) ≠ 0 := by
  let a : Fin 4 → K := Fin.snoc (0 : Fin 3 → K) 1
  have ha : a ≠ 0 := by
    intro hz
    have he := congrFun hz (Fin.last 3)
    apply (one_ne_zero : (1 : K) ≠ 0)
    simpa only [a, Fin.snoc_last, Pi.zero_apply] using he
  have haxis : w ⬝ᵥ (fun i => algebraMap K F (a i)) = 0 := by
    dsimp only [dotProduct]
    rw [Fin.sum_univ_castSucc]
    simp only [a, Fin.snoc_castSucc, Pi.zero_apply, map_zero, mul_zero,
      Finset.sum_const_zero, Fin.snoc_last, map_one, mul_one, zero_add, hvertex]
  have hker := normal_constant_relation_space_eq_span_characteristic D w hLI a ha
    (constant_normal_relation_mem_characteristic D w a haxis)
  intro hz
  have hmem : Fin.snoc b 0 ∈ LinearMap.ker (Fintype.linearCombination K w) := by
    change Fintype.linearCombination K w (Fin.snoc b 0) = 0
    simp only [Fintype.linearCombination_apply, Algebra.smul_def]
    rw [Fin.sum_univ_castSucc]
    simpa only [Fin.snoc_castSucc, Fin.snoc_last, map_zero, zero_mul, add_zero,
      mul_comm] using hz
  rw [hker] at hmem
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hmem
  apply hb
  funext i
  have he := congrFun hc i.castSucc
  simpa only [Pi.smul_apply, a, Fin.snoc_castSucc, Pi.zero_apply, smul_eq_mul,
    mul_zero] using he.symm

/-- The generic normal plane meets every original vertex line at
the vertex while containing no such whole line. -/
theorem independent_normal_jets_vertex_line_plane_incidence
    (D : Derivation K F F) (w : Fin 4 → F)
    (hLI : LinearIndependent F (normalCharacteristicMatrix D w).row)
    (hvertex : w (Fin.last 3) = 0)
    (b : Fin 3 → K) (hb : b ≠ 0) (j : Fin 3) (hj : b j ≠ 0) :
    aeval (Fin.snoc (0 : Fin 3 → F) 1) (linearFormPolynomial w) = 0 ∧
      linearFormPolynomial w ∉ vertexLinePrime (fun i => algebraMap K F (b i)) j := by
  constructor
  · simp only [linearFormPolynomial, map_sum, map_mul, aeval_C, aeval_X,
      Algebra.algebraMap_self, RingHom.id_apply]
    rw [Fin.sum_univ_castSucc]
    simp only [Fin.snoc_castSucc, Pi.zero_apply, mul_zero, Finset.sum_const_zero,
      Fin.snoc_last, mul_one, zero_add, hvertex]
  · exact vertexLinePrime_linearForm_not_mem _ j
      ((_root_.map_ne_zero (algebraMap K F)).mpr hj) w
      (independent_normal_jets_transverse_constant_pairing_ne_zero D w hLI hvertex b hb)

end DimensionFourDependence
