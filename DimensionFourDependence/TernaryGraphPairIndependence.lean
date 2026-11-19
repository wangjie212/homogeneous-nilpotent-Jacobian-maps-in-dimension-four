import DimensionFourDependence.TernaryGraphCovectorRestriction
import DimensionFourDependence.RankSelectionOfIndependentOutputs
import DimensionFourDependence.FixedConeCoordinateConjugacy

/-! # A transverse original frame preserves an independent output pair -/

namespace DimensionFourDependence

open MvPolynomial Matrix

universe u
set_option maxHeartbeats 2100000

variable {K : Type u} [Field K] [CharZero K] {n m r : ℕ}

/-- Full row rank implies algebraic independence of the actual family. -/
theorem rationalJacobian_full_row_rank_algebraicIndependent
    (H : Fin m → FractionRing (MvPolynomial (Fin n) K))
    (hR : (rationalJacobian H).rank = m) : AlgebraicIndependent K H := by
  obtain ⟨s, hs, hi, _⟩ := jacobian_rank_selects_independent_output_indices H hR
  let p := Equiv.ofBijective s ⟨hs, Finite.surjective_of_injective hs⟩
  have he : (fun i => H (s i)) ∘ p.symm = H := by
    funext i
    change H (p (p.symm i)) = H i
    rw [p.apply_symm_apply]
  rw [← he]
  exact hi.comp p.symm p.symm.injective

omit [CharZero K] in
/-- An original constant matrix multiplies the rational Jacobian on
the left when it combines the outputs. -/
theorem rationalJacobian_constant_linear_output
    (H : Fin m → FractionRing (MvPolynomial (Fin n) K))
    (C₀ : Matrix (Fin r) (Fin m) K) :
    let E := FractionRing (MvPolynomial (Fin n) K)
    rationalJacobian (C₀.map (algebraMap K E) *ᵥ H) =
      C₀.map (algebraMap K E) * rationalJacobian H := by
  let E := FractionRing (MvPolynomial (Fin n) K)
  funext i j
  let d := rationalPartial (K := K) j
  change d (∑ k, algebraMap K E (C₀ i k) * H k) =
    ∑ k, algebraMap K E (C₀ i k) * d (H k)
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro k _
  rw [d.leibniz, d.map_algebraMap, smul_zero, add_zero, smul_eq_mul]

local notation "R₃" => MvPolynomial (Fin 3) K
local notation "F" => FractionRing R₃
local notation "ι" => (algebraMap R₃ F)

/-- The two restrictions to the direction plane are exactly the
matrix on the independent Jacobian rows. -/
theorem ternary_graph_restricted_covector_jacobian
    (Y : Fin 2 → F) (hY : AlgebraicIndependent K Y) (w : coefficientField (K := K) Y)
    (C₀ : Matrix (Fin 2) (Fin 3) K) :
    let E := coefficientField (K := K) Y
    let A : Matrix (Fin 2) (Fin 2) E := fun i => ternaryGraphRestrictedCovector
      (coefficientPartial Y hY 0 w) (coefficientPartial Y hY 1 w) (C₀ i)
    rationalJacobian (C₀.map (algebraMap K F) *ᵥ (![Y 0,Y 1,(w : F)] : Fin 3 → F)) =
      A.map (algebraMap E F) * rationalJacobian Y := by
  let E := coefficientField (K := K) Y
  let : IsScalarTower K E F := coefficientFieldScalarTower Y
  let p := coefficientPartial Y hY 0 w
  let q := coefficientPartial Y hY 1 w
  dsimp only
  rw [rationalJacobian_constant_linear_output, ternaryGraph_rationalJacobian]
  funext i j
  simp only [Matrix.mul_apply, Fin.sum_univ_three, Fin.sum_univ_two, Matrix.map_apply]
  change algebraMap K F (C₀ i 0) * ternaryRationalGradient (Y 0) j +
      algebraMap K F (C₀ i 1) * ternaryRationalGradient (Y 1) j +
      algebraMap K F (C₀ i 2) *
        ((p : F) * ternaryRationalGradient (Y 0) j + (q : F) * ternaryRationalGradient (Y 1) j) =
    algebraMap E F (algebraMap K E (C₀ i 0) + algebraMap K E (C₀ i 2) * p) * ternaryRationalGradient (Y 0) j +
      algebraMap E F (algebraMap K E (C₀ i 1) + algebraMap K E (C₀ i 2) * q) * ternaryRationalGradient (Y 1) j
  simp only [map_add, map_mul, ← IsScalarTower.algebraMap_apply K E F,
    IntermediateField.algebraMap_apply]
  ring

/-- An original frame whose first two rows restrict independently to
the direction plane also selects algebraically independent outputs. -/
theorem ternary_graph_transverse_frame_first_two_outputs_independent
    (T S : Matrix (Fin 3) (Fin 3) K) (hTS : T * S = 1) (hST : S * T = 1)
    (H : Fin 3 → R₃) (Y : Fin 2 → F) (hY : AlgebraicIndependent K Y)
    (hpair : ∀ i : Fin 2, Y i = ι (H i.castSucc))
    (w : coefficientField (K := K) Y) (hw : (w : F) = ι (H 2))
    (hA : (show Matrix (Fin 2) (Fin 2) (coefficientField (K := K) Y) from fun i =>
      ternaryGraphRestrictedCovector (coefficientPartial Y hY 0 w)
        (coefficientPartial Y hY 1 w) (S i.castSucc)).det ≠ 0) :
    AlgebraicIndependent K (fun i : Fin 2 => ι (linearPolynomialConjugate T S H i.castSucc)) := by
  let E := coefficientField (K := K) Y
  let C₀ : Matrix (Fin 2) (Fin 3) K := fun i j => S i.castSucc j
  let A : Matrix (Fin 2) (Fin 2) E := fun i => ternaryGraphRestrictedCovector
    (coefficientPartial Y hY 0 w) (coefficientPartial Y hY 1 w) (C₀ i)
  let V := C₀.map (algebraMap K F) *ᵥ (![Y 0,Y 1,(w : F)] : Fin 3 → F)
  have hdet : IsUnit (A.map (algebraMap E F)).det := by
    change IsUnit ((algebraMap E F).mapMatrix A).det
    rw [← RingHom.map_det]
    exact (isUnit_iff_ne_zero.mpr hA).map (algebraMap E F)
  have hJV : rationalJacobian V = A.map (algebraMap E F) * rationalJacobian Y :=
    ternary_graph_restricted_covector_jacobian Y hY w C₀
  have hR : (rationalJacobian V).rank = 2 := by
    rw [hJV, Matrix.rank_mul_eq_right_of_isUnit_det _ _ hdet, rationalJacobian_rank_of_independent Y hY]
  have hV := rationalJacobian_full_row_rank_algebraicIndependent V hR
  let e := matrixSourceFractionEquiv T S hTS hST
  have hw' : (![Y 0,Y 1,(w : F)] : Fin 3 → F) = fun j => ι (H j) := by
    funext j
    fin_cases j
    · exact hpair 0
    · exact hpair 1
    · exact hw
  have he : (fun i : Fin 2 => ι (linearPolynomialConjugate T S H i.castSucc)) = e.toAlgHom ∘ V := by
    funext i
    rw [linearPolynomialConjugate_source_value T S hTS hST H]
    change ∑ k, algebraMap K F (S i.castSucc k) * e (ι (H k)) =
      e ((C₀.map (algebraMap K F) *ᵥ (![Y 0,Y 1,(w : F)] : Fin 3 → F)) i)
    rw [hw']
    change _ = e (∑ k, algebraMap K F (S i.castSucc k) * ι (H k))
    simp only [map_sum, map_mul, AlgEquiv.commutes]
  rw [he]
  exact hV.map' (f := e.toAlgHom) e.injective

end DimensionFourDependence
