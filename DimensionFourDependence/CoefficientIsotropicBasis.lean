import DimensionFourDependence.RankTwoIsotropicBasis
import DimensionFourDependence.CubicResidueDescent

/-! # Isotropic bases over extensions of the actual coefficient field

The rank hypothesis is needed only over the original coefficient field.
An orthogonal pair there splits over algebraically closed constants,
and its nonzero mixed pairing proves independence after scalar extension.
-/

namespace DimensionFourDependence

open Matrix Module

variable {F E G : Type*} [Field F] [CharZero F] [Field E] [CharZero E]
    [IsAlgClosed E] [Algebra F E]

/-- The rank-two radial form acquires an isotropic basis over any
algebraically closed extension, with no rank-preservation hypothesis to supply. -/
theorem rank_two_radial_isotropic_basis_over
    (T : Matrix (Fin 3) (Fin 3) F) (hT : ∀ i j, T i j = T j i) (hrank : T.rank = 2)
    (Y : Fin 3 → F) (hY0 : Y ≠ 0) (hY : ∀ j, (∑ i, Y i * T i j) = 0) :
    ∃ Z W : Fin 3 → E, matrixBilinearPairing (T.map (algebraMap F E)) Z Z = 0 ∧
      matrixBilinearPairing (T.map (algebraMap F E)) W W = 0 ∧
      matrixBilinearPairing (T.map (algebraMap F E)) Z W ≠ 0 ∧
      LinearIndependent E ![(fun i => algebraMap F E (Y i)), Z, W] ∧
      Submodule.span E (Set.range ![(fun i => algebraMap F E (Y i)), Z, W]) = ⊤ := by
  have hTY : T *ᵥ Y = 0 := by
    funext j
    change (∑ i, T j i * Y i) = 0
    calc
      _ = ∑ i, Y i * T i j := Finset.sum_congr rfl (fun i _ => by rw [hT j i, mul_comm])
      _ = 0 := hY j
  obtain ⟨u, v, hu, hv, huv⟩ := rank_two_exists_orthogonal_nonisotropic_pair T hT hrank Y hY0 hTY
  have hTE (i j : Fin 3) : T.map (algebraMap F E) i j = T.map (algebraMap F E) j i :=
    congrArg (algebraMap F E) (hT i j)
  have huE : matrixBilinearPairing (T.map (algebraMap F E))
      (fun i => algebraMap F E (u i)) (fun i => algebraMap F E (u i)) ≠ 0 := by
    rw [matrixBilinearPairing_map]
    simpa only [map_zero] using (algebraMap F E).injective.ne hu
  have hvE : matrixBilinearPairing (T.map (algebraMap F E))
      (fun i => algebraMap F E (v i)) (fun i => algebraMap F E (v i)) ≠ 0 := by
    rw [matrixBilinearPairing_map]
    simpa only [map_zero] using (algebraMap F E).injective.ne hv
  have huvE : matrixBilinearPairing (T.map (algebraMap F E))
      (fun i => algebraMap F E (u i)) (fun i => algebraMap F E (v i)) = 0 := by
    rw [matrixBilinearPairing_map, huv, map_zero]
  obtain ⟨Z, W, hZ, hW, hκ⟩ := orthogonal_nonisotropic_pair_splits
    (T.map (algebraMap F E)) hTE _ _ huE hvE huvE
  have hYE0 : (fun i => algebraMap F E (Y i)) ≠ 0 := by
    intro hz
    apply hY0
    funext i
    apply (algebraMap F E).injective
    simpa only [map_zero, Pi.zero_apply] using congrFun hz i
  have hli := radical_isotropic_triple_independent (T.map (algebraMap F E)) hTE
    (fun i => algebraMap F E (Y i)) Z W hYE0 (matrixBilinearPairing_radical_map T Y hY) hZ hW hκ
  refine ⟨Z, W, hZ, hW, hκ, hli, ?_⟩
  apply Submodule.eq_top_iff_finrank_eq.mpr
  simpa only [Module.finrank_pi, Fintype.card_fin] using finrank_span_eq_card hli

section Coordinates

variable [Field G] [Algebra E G]

omit [Field F] [CharZero F] [Algebra F E] [IsAlgClosed E] [CharZero E] in
/-- A radial isotropic basis gives coordinates over every further
field extension, with the scalar extension of independence derived. -/
theorem radial_isotropic_coordinates_over
    (T : Matrix (Fin 3) (Fin 3) E) (hT : ∀ i j, T i j = T j i)
    (Y Z W : Fin 3 → E) (hY0 : Y ≠ 0) (hY : ∀ j, (∑ i, Y i * T i j) = 0)
    (hZ : matrixBilinearPairing T Z Z = 0) (hW : matrixBilinearPairing T W W = 0)
    (hκ : matrixBilinearPairing T Z W ≠ 0) (x : Fin 3 → G) :
    ∃ τ s t : G, ∀ i, x i = τ * algebraMap E G (Y i) +
      s * algebraMap E G (Z i) + t * algebraMap E G (W i) := by
  have hYG0 : (fun i => algebraMap E G (Y i)) ≠ 0 := by
    intro hz
    apply hY0
    funext i
    apply (algebraMap E G).injective
    simpa only [map_zero, Pi.zero_apply] using congrFun hz i
  have hZG : matrixBilinearPairing (T.map (algebraMap E G))
      (fun i => algebraMap E G (Z i)) (fun i => algebraMap E G (Z i)) = 0 := by
    rw [matrixBilinearPairing_map, hZ, map_zero]
  have hWG : matrixBilinearPairing (T.map (algebraMap E G))
      (fun i => algebraMap E G (W i)) (fun i => algebraMap E G (W i)) = 0 := by
    rw [matrixBilinearPairing_map, hW, map_zero]
  have hκG : matrixBilinearPairing (T.map (algebraMap E G))
      (fun i => algebraMap E G (Z i)) (fun i => algebraMap E G (W i)) ≠ 0 := by
    rw [matrixBilinearPairing_map]
    simpa only [map_zero] using (algebraMap E G).injective.ne hκ
  have hli := radical_isotropic_triple_independent (T.map (algebraMap E G))
    (fun i j => congrArg (algebraMap E G) (hT i j))
    (fun i => algebraMap E G (Y i)) (fun i => algebraMap E G (Z i))
    (fun i => algebraMap E G (W i)) hYG0 (matrixBilinearPairing_radical_map T Y hY) hZG hWG hκG
  have hspan : Submodule.span G (Set.range ![(fun i => algebraMap E G (Y i)),
      (fun i => algebraMap E G (Z i)), (fun i => algebraMap E G (W i))]) = ⊤ := by
    apply Submodule.eq_top_iff_finrank_eq.mpr
    simpa only [Module.finrank_pi, Fintype.card_fin] using finrank_span_eq_card hli
  have hx : x ∈ Submodule.span G (Set.range ![(fun i => algebraMap E G (Y i)),
      (fun i => algebraMap E G (Z i)), (fun i => algebraMap E G (W i))]) := by rw [hspan]; trivial
  obtain ⟨g, hg⟩ := (Submodule.mem_span_range_iff_exists_fun (R := G)).mp hx
  refine ⟨g 0, g 1, g 2, ?_⟩
  intro i
  have he := congrFun hg.symm i
  simpa [Fin.sum_univ_succ, Pi.add_apply, Pi.smul_apply, smul_eq_mul, add_assoc] using he

end Coordinates

variable {K : Type*} [Field K] [CharZero K]

omit [Field F] [CharZero F] [Field E] [CharZero E] [IsAlgClosed E] [Algebra F E] in
/-- The actual coefficient Hessian supplies the two isotropic
directions over any algebraically closed coefficient extension once its rank is two. -/
theorem coefficientHessian_exists_isotropic_basis_over
    (Y : Fin 3 → FractionRing (MvPolynomial (Fin 4) K)) (hY : AlgebraicIndependent K Y)
    (h : coefficientField (K := K) Y) (hh : coefficientEuler Y hY h = h)
    (hrank : (coefficientHessian Y hY h).rank = 2)
    (A : Type*) [Field A] [CharZero A] [IsAlgClosed A] [Algebra (coefficientField (K := K) Y) A] :
    ∃ Z W : Fin 3 → A,
      matrixBilinearPairing ((coefficientHessian Y hY h).map (algebraMap (coefficientField (K := K) Y) A)) Z Z = 0 ∧
      matrixBilinearPairing ((coefficientHessian Y hY h).map (algebraMap (coefficientField (K := K) Y) A)) W W = 0 ∧
      matrixBilinearPairing ((coefficientHessian Y hY h).map (algebraMap (coefficientField (K := K) Y) A)) Z W ≠ 0 ∧
      LinearIndependent A ![(fun i => algebraMap (coefficientField (K := K) Y) A (coefficientCoordinate (K := K) Y i)), Z, W] ∧
      Submodule.span A (Set.range ![(fun i => algebraMap (coefficientField (K := K) Y) A (coefficientCoordinate (K := K) Y i)), Z, W]) = ⊤ := by
  have hy0 : coefficientCoordinate (K := K) Y ≠ 0 := by
    intro he
    apply (hY.transcendental 0).ne_zero
    have hz := congrArg (algebraMap (coefficientField (K := K) Y) (FractionRing (MvPolynomial (Fin 4) K))) (congrFun he 0)
    simpa only [Pi.zero_apply, map_zero, IntermediateField.algebraMap_apply, coefficientCoordinate_coe] using hz
  exact rank_two_radial_isotropic_basis_over (E := A) (coefficientHessian Y hY h)
    (coefficientHessian_symmetric Y hY h) hrank (coefficientCoordinate (K := K) Y) hy0
    (coefficientHessian_radial_contraction Y hY h hh)

end DimensionFourDependence
