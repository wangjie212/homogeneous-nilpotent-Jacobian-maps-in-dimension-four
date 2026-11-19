import DimensionFourDependence.CoefficientIsotropicBasis
import DimensionFourDependence.CoefficientIsotropicLine

/-! # Rank two persists under extension of a radial coefficient form

An orthogonal nonisotropic pair gives two independent matrix images,
while a nonzero radial kernel vector bounds the rank above by two.
Both witnesses persist under every field extension.
-/

namespace DimensionFourDependence

open Matrix Module

variable {F E : Type*} [Field F] [Field E] [Algebra F E]

/-- A symmetric three-variable form with a nonzero radial radical
and an orthogonal nonisotropic pair has rank exactly two. -/
theorem rank_two_of_radical_orthogonal_pair
    (T : Matrix (Fin 3) (Fin 3) F) (hT : ∀ i j, T i j = T j i)
    (Y u v : Fin 3 → F) (hY0 : Y ≠ 0) (hTY : T *ᵥ Y = 0)
    (hu : matrixBilinearPairing T u u ≠ 0) (hv : matrixBilinearPairing T v v ≠ 0)
    (huv : matrixBilinearPairing T u v = 0) : T.rank = 2 := by
  have hvu : matrixBilinearPairing T v u = 0 :=
    (matrixBilinearPairing_symmetric T hT v u).trans huv
  have hli : LinearIndependent F ![T *ᵥ u, T *ᵥ v] := by
    apply Fintype.linearIndependent_iff.mpr
    intro c hc i
    have he : c 0 • (T *ᵥ u) + c 1 • (T *ᵥ v) = 0 := by
      simpa only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons] using hc
    have heu := congrArg (fun w => u ⬝ᵥ w) he
    simp only [dotProduct_add, dotProduct_smul, smul_eq_mul, dotProduct_zero,
      ← matrixBilinearPairing_eq_dot_mulVec, huv, mul_zero, add_zero] at heu
    have he0 : c 0 = 0 := (mul_eq_zero.mp heu).resolve_right hu
    have hev := congrArg (fun w => v ⬝ᵥ w) he
    simp only [dotProduct_add, dotProduct_smul, smul_eq_mul, dotProduct_zero,
      ← matrixBilinearPairing_eq_dot_mulVec, hvu, mul_zero, zero_add] at hev
    have he1 : c 1 = 0 := (mul_eq_zero.mp hev).resolve_right hv
    fin_cases i <;> assumption
  have hle : Submodule.span F (Set.range ![T *ᵥ u, T *ᵥ v]) ≤ LinearMap.range T.toLin' := by
    apply Submodule.span_le.mpr
    rintro _ ⟨i, rfl⟩
    fin_cases i
    · exact ⟨u, rfl⟩
    · exact ⟨v, rfl⟩
  have hdim : finrank F (Submodule.span F (Set.range ![T *ᵥ u, T *ᵥ v])) = 2 := by
    simpa using finrank_span_eq_card hli
  have hb := Submodule.finrank_mono hle
  have hkpos : 0 < finrank F (LinearMap.ker T.toLin') := by
    apply Module.finrank_pos_iff_exists_ne_zero.mpr
    exact ⟨⟨Y, hTY⟩, fun he => hY0 (congrArg Subtype.val he)⟩
  have hd := LinearMap.finrank_range_add_finrank_ker T.toLin'
  have hr : finrank F (LinearMap.range T.toLin') = T.rank := rfl
  simp only [Module.finrank_pi, Fintype.card_fin] at hd
  omega

variable [CharZero F]

/-- A rank-two symmetric form with a nonzero radial radical stays
rank two after an arbitrary field extension. -/
theorem radial_rank_two_map
    (T : Matrix (Fin 3) (Fin 3) F) (hT : ∀ i j, T i j = T j i) (hrank : T.rank = 2)
    (Y : Fin 3 → F) (hY0 : Y ≠ 0) (hTY : T *ᵥ Y = 0) :
    (T.map (algebraMap F E)).rank = 2 := by
  obtain ⟨u, v, hu, hv, huv⟩ := rank_two_exists_orthogonal_nonisotropic_pair T hT hrank Y hY0 hTY
  have hYE : (fun i => algebraMap F E (Y i)) ≠ 0 := by
    intro hz
    apply hY0
    funext i
    apply (algebraMap F E).injective
    simpa only [Pi.zero_apply, map_zero] using congrFun hz i
  have hTYE : T.map (algebraMap F E) *ᵥ (fun i => algebraMap F E (Y i)) = 0 := by
    funext i
    have he := congrArg (algebraMap F E) (congrFun hTY i)
    simpa only [Matrix.mulVec, dotProduct, map_sum, map_mul, map_zero, Pi.zero_apply, Matrix.map_apply] using he
  apply rank_two_of_radical_orthogonal_pair (T.map (algebraMap F E))
    (fun i j => congrArg (algebraMap F E) (hT i j)) (fun i => algebraMap F E (Y i))
    (fun i => algebraMap F E (u i)) (fun i => algebraMap F E (v i)) hYE hTYE
  · rw [matrixBilinearPairing_map]
    simpa only [map_zero] using (algebraMap F E).injective.ne hu
  · rw [matrixBilinearPairing_map]
    simpa only [map_zero] using (algebraMap F E).injective.ne hv
  · rw [matrixBilinearPairing_map, huv, map_zero]

variable {K : Type*} [Field K] [CharZero K]

omit [Field F] [CharZero F] [Field E] [Algebra F E] in
/-- The actual rank-two coefficient Hessian stays rank two over every
further coefficient field, with its radial kernel and nonzero vector derived. -/
theorem coefficientHessian_rank_two_map
    (Y : Fin 3 → FractionRing (MvPolynomial (Fin 4) K)) (hY : AlgebraicIndependent K Y)
    (h : coefficientField (K := K) Y) (hh : coefficientEuler Y hY h = h)
    (hrank : (coefficientHessian Y hY h).rank = 2)
    (A : Type*) [Field A] [Algebra (coefficientField (K := K) Y) A] :
    ((coefficientHessian Y hY h).map (algebraMap (coefficientField (K := K) Y) A)).rank = 2 := by
  have hY0 : coefficientCoordinate (K := K) Y ≠ 0 := by
    intro hz
    apply (hY.transcendental 0).ne_zero
    simpa only [coefficientCoordinate_coe, IntermediateField.coe_zero, Pi.zero_apply] using
      congrArg (fun z : coefficientField (K := K) Y => (z : FractionRing (MvPolynomial (Fin 4) K))) (congrFun hz 0)
  apply radial_rank_two_map (coefficientHessian Y hY h) (coefficientHessian_symmetric Y hY h)
    hrank (coefficientCoordinate (K := K) Y) hY0
  exact coefficientHessian_radial_mulVec_map Y hY (coefficientField (K := K) Y) h hh

end DimensionFourDependence
