import DimensionFourDependence.FiberPrimeHeight
import DimensionFourDependence.ComponentGenericPoint

/-! # The actual prime ideal of a line through the fourth-axis vertex

The line has two free affine-cone coordinates. Its prime is the exact
kernel of the original-coordinate parametrization. An explicit nonzero
hyperplane prime strictly below it gives height at least two. These
facts identify any height-at-most-two prime containing its equations.
-/

namespace DimensionFourDependence

open MvPolynomial

set_option maxHeartbeats 2500000

variable {K : Type*} [Field K]

/-- The actual two-coordinate parametrization of a vertex line,
normalized at a specified nonzero transverse direction coordinate. -/
noncomputable def vertexLineParameterHom (b : Fin 3 → K) (j : Fin 3) :
    MvPolynomial (Fin 4) K →ₐ[K] MvPolynomial (Fin 2) K :=
  aeval (Fin.snoc (fun i : Fin 3 => C (b i / b j) * X (0 : Fin 2)) (X 1))

/-- The prime of the full original vertex line, as an exact kernel. -/
noncomputable def vertexLinePrime (b : Fin 3 → K) (j : Fin 3) :
    Ideal (MvPolynomial (Fin 4) K) := RingHom.ker (vertexLineParameterHom b j).toRingHom

/-- The parametrized line has an integral original coordinate ring. -/
@[instance] theorem vertexLinePrime_isPrime (b : Fin 3 → K) (j : Fin 3) :
    (vertexLinePrime b j).IsPrime := RingHom.ker_isPrime _

/-- A normalized original line equation belongs to the exact line prime. -/
theorem vertexLinePrime_coordinate_relation
    (b : Fin 3 → K) (j : Fin 3) (hj : b j ≠ 0) (i : Fin 3) :
    X i.castSucc - C (b i / b j) * X j.castSucc ∈ vertexLinePrime b j := by
  change vertexLineParameterHom b j _ = 0
  simp [vertexLineParameterHom, hj]

/-- The transverse pivot remains a nonzero free coordinate on the line. -/
theorem vertexLinePrime_pivot_not_mem
    (b : Fin 3 → K) (j : Fin 3) (hj : b j ≠ 0) :
    X j.castSucc ∉ vertexLinePrime b j := by
  intro h
  change vertexLineParameterHom b j (X j.castSucc) = 0 at h
  have he : (X (0 : Fin 2) : MvPolynomial (Fin 2) K) = 0 := by
    simpa [vertexLineParameterHom, hj] using h
  exact X_ne_zero _ he

/-- A coordinate equation with a distinct free pivot is nonzero. -/
theorem coordinate_difference_ne_zero {n : ℕ}
    (i j : Fin n) (hij : i ≠ j) (a : K) :
    (X i - C a * X j : MvPolynomial (Fin n) K) ≠ 0 := by
  intro hz
  have he := congrArg (aeval (Pi.single i (1 : K))) hz
  simpa [Pi.single_apply, hij, hij.symm] using he

/-- An explicit nonzero hyperplane prime strictly below the line
prime constructs its height-at-least-two bound. -/
theorem vertexLinePrime_height_ge_two
    (b : Fin 3 → K) (j : Fin 3) (hj : b j ≠ 0) :
    2 ≤ (vertexLinePrime b j).height := by
  obtain ⟨i, k, hij, hkj, hki⟩ : ∃ i k : Fin 3, i ≠ j ∧ k ≠ j ∧ k ≠ i := by
    fin_cases j
    · exact ⟨1, 2, by decide, by decide, by decide⟩
    · exact ⟨0, 2, by decide, by decide, by decide⟩
    · exact ⟨0, 1, by decide, by decide, by decide⟩
  have hij4 : i.castSucc ≠ j.castSucc := fun h => hij (Fin.castSucc_injective 3 h)
  have hkj4 : k.castSucc ≠ j.castSucc := fun h => hkj (Fin.castSucc_injective 3 h)
  have hki4 : k.castSucc ≠ i.castSucc := fun h => hki (Fin.castSucc_injective 3 h)
  let f : MvPolynomial (Fin 4) K →ₐ[K] MvPolynomial (Fin 4) K :=
    aeval (fun ℓ => if ℓ = i.castSucc then C (b i / b j) * X j.castSucc else X ℓ)
  let J : Ideal (MvPolynomial (Fin 4) K) := RingHom.ker f.toRingHom
  let : J.IsPrime := RingHom.ker_isPrime _
  have hpJ : X i.castSucc - C (b i / b j) * X j.castSucc ∈ J := by
    change f _ = 0
    simp [f, hij4.symm]
  have hJ0 : J ≠ ⊥ := by
    intro he
    rw [he, Ideal.mem_bot] at hpJ
    exact coordinate_difference_ne_zero i.castSucc j.castSucc hij4 _ hpJ
  have hcomp : (vertexLineParameterHom b j).comp f = vertexLineParameterHom b j := by
    apply MvPolynomial.algHom_ext
    intro ℓ
    by_cases hℓ : ℓ = i.castSucc
    · subst ℓ
      simp [f, vertexLineParameterHom, hj]
    · simp [f, hℓ]
  have hle : J ≤ vertexLinePrime b j := by
    intro P hP
    change vertexLineParameterHom b j P = 0
    have he := DFunLike.congr_fun hcomp P
    change vertexLineParameterHom b j (f P) = vertexLineParameterHom b j P at he
    change f P = 0 at hP
    rw [hP, map_zero] at he
    exact he.symm
  have hnot : X k.castSucc - C (b k / b j) * X j.castSucc ∉ J := by
    intro h
    change f _ = 0 at h
    apply coordinate_difference_ne_zero k.castSucc j.castSucc hkj4 (b k / b j)
    simpa [f, hki4, hij4.symm] using h
  have hlt : J < vertexLinePrime b j := lt_of_le_of_ne hle (by
    intro he
    exact hnot (he ▸ vertexLinePrime_coordinate_relation b j hj k))
  have hpos : 1 ≤ J.height := Order.one_le_iff_ne_zero.mpr
    ((Ideal.height_eq_zero_iff_eq_bot (I := J)).not.mpr hJ0)
  have hstep := Ideal.height_add_one_le_of_lt_of_isPrime hlt
  calc
    (2 : ℕ∞) = 1 + 1 := rfl
    _ ≤ J.height + 1 := add_le_add hpos le_rfl
    _ ≤ (vertexLinePrime b j).height := hstep

end DimensionFourDependence
