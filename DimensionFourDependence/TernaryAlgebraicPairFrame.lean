import DimensionFourDependence.TernaryConicChartTransport
import DimensionFourDependence.LinearConjugacyComposition

/-! # The algebraic linear combination becomes the actual last output -/

namespace DimensionFourDependence

open MvPolynomial Matrix

universe u
set_option maxHeartbeats 2100000

variable {K E : Type u} [Field K] [Field E] [Algebra K E]

theorem source_equiv_isAlgebraic_over_mapped_singleton
    (f : E ≃ₐ[K] E) (x y : E)
    (h : IsAlgebraic (IntermediateField.adjoin K {x}) y) :
    IsAlgebraic (IntermediateField.adjoin K {f x}) (f y) := by
  let B := IntermediateField.adjoin K {x}
  let e := IntermediateField.intermediateFieldMap f B
  have hmap : B.map f.toAlgHom = IntermediateField.adjoin K {f x} := by
    change (IntermediateField.adjoin K {x}).map f.toAlgHom = _
    rw [IntermediateField.adjoin_map, Set.image_singleton]
    rfl
  have hc : (algebraMap (B.map f.toAlgHom) E).comp e.toRingHom =
      f.toRingHom.comp (algebraMap B E) := by
    ext a
    rfl
  rw [← hmap]
  exact (isAlgebraic_ringHom_iff_of_comp_eq e.toRingEquiv f.toRingHom f.injective hc).mpr h

variable [CharZero K]
local notation "R₃" => MvPolynomial (Fin 3) K
local notation "F" => FractionRing R₃
local notation "ι" => (algebraMap R₃ F)

/-- An original linear shear changes a dependent linear combination
into the actual third component and preserves the independent pair. -/
theorem ternary_conjugate_subtracts_second_from_algebraic_last_output
    (H : Fin 3 → R₃) (μ : K)
    (hY : AlgebraicIndependent K (ternaryRationalOutputPair (K := K) H))
    (h : IsAlgebraic (IntermediateField.adjoin K {ι (H 0)}) (ι (H 2 - C μ * H 1))) :
    ∃ T S : Matrix (Fin 3) (Fin 3) K, T * S = 1 ∧ S * T = 1 ∧
      let G := linearPolynomialConjugate T S H
      AlgebraicIndependent K (ternaryRationalOutputPair (K := K) G) ∧
        IsAlgebraic (IntermediateField.adjoin K {ι (G 0)}) (ι (G 2)) := by
  let T : Matrix (Fin 3) (Fin 3) K := !![1,0,0; 0,1,0; 0,μ,1]
  let S : Matrix (Fin 3) (Fin 3) K := !![1,0,0; 0,1,0; 0,-μ,1]
  have hTS : T * S = 1 := by
    funext i j
    fin_cases i <;> fin_cases j <;> simp [T, S, Matrix.mul_apply, Matrix.one_apply, Fin.sum_univ_three]
  have hST : S * T = 1 := by
    funext i j
    fin_cases i <;> fin_cases j <;> simp [T, S, Matrix.mul_apply, Matrix.one_apply, Fin.sum_univ_three]
  let f := matrixSourceFractionEquiv T S hTS hST
  let G := linearPolynomialConjugate T S H
  have h₀ : ι (G 0) = f (ι (H 0)) := by
    change ι (linearPolynomialConjugate T S H 0) = _
    rw [linearPolynomialConjugate_source_value T S hTS hST H 0, Fin.sum_univ_three]
    simp [S, f]
  have h₁ : ι (G 1) = f (ι (H 1)) := by
    change ι (linearPolynomialConjugate T S H 1) = _
    rw [linearPolynomialConjugate_source_value T S hTS hST H 1, Fin.sum_univ_three]
    simp [S, f]
  have h₂ : ι (G 2) = f (ι (H 2 - C μ * H 1)) := by
    change ι (linearPolynomialConjugate T S H 2) = _
    rw [linearPolynomialConjugate_source_value T S hTS hST H 2, Fin.sum_univ_three]
    have hc : ι (C μ) = algebraMap K F μ := by
      rw [← algebraMap_eq, ← IsScalarTower.algebraMap_apply K R₃ F]
    rw [map_sub (ι), map_mul (ι), hc, map_sub f, map_mul f, f.commutes]
    simp [S, f]
    ring
  refine ⟨T, S, hTS, hST, ?_, ?_⟩
  · have he : ternaryRationalOutputPair (K := K) G =
        f.toAlgHom ∘ ternaryRationalOutputPair (K := K) H := by
      funext i
      fin_cases i
      · exact h₀
      · exact h₁
    change AlgebraicIndependent K (ternaryRationalOutputPair (K := K) G)
    rw [he]
    exact hY.map' (f := f.toAlgHom) f.injective
  · change IsAlgebraic (IntermediateField.adjoin K {ι (G 0)}) (ι (G 2))
    rw [h₀, h₂]
    exact source_equiv_isAlgebraic_over_mapped_singleton f _ _ h

end DimensionFourDependence
