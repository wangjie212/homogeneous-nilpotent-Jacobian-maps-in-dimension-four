import DimensionFourDependence.FirstInvariant
import DimensionFourDependence.OutputSelection

/-! # The first invariant for an arbitrary nilpotent rank-three map

The selected output components and the source coordinates are given the
same ordering. Keeping that ordering explicit avoids replacing the actual
source function field by an isomorphic copy.
-/

namespace DimensionFourDependence

open Matrix

variable {K : Type*} [Field K] [CharZero K]

/-- The first fiber invariant in a simultaneously reordered coordinate chart. -/
noncomputable def firstFiberInvariantInChart (p : Equiv.Perm (Fin 4))
    (Y : Fin 3 → FractionRing (MvPolynomial (Fin 4) K)) (hY : AlgebraicIndependent K Y)
    (h : coefficientField (K := K) Y) : FractionRing (MvPolynomial (Fin 4) K) :=
  rationalCoordinate (K := K) (p 3) - ∑ i : Fin 3,
    (coefficientPartial (K := K) Y hY i h : FractionRing (MvPolynomial (Fin 4) K)) *
      rationalCoordinate (K := K) (p i.castSucc)

/-- The same constant-field argument works in every reordered chart. -/
theorem firstFiberInvariantInChart_mem_of_frame (p : Equiv.Perm (Fin 4))
    (Y : Fin 3 → FractionRing (MvPolynomial (Fin 4) K)) (hY : AlgebraicIndependent K Y)
    (h : coefficientField (K := K) Y)
    (u : Fin 4 → FractionRing (MvPolynomial (Fin 4) K)) (hu0 : u ≠ 0)
    (hker : rationalJacobian Y *ᵥ u = 0)
    (hframe : u (p 3) = ∑ i : Fin 3,
      (coefficientPartial (K := K) Y hY i h : FractionRing (MvPolynomial (Fin 4) K)) *
        u (p i.castSucc)) :
    firstFiberInvariantInChart p Y hY h ∈ coefficientField (K := K) Y := by
  change firstFiberInvariantInChart p Y hY h ∈ (coefficientField (K := K) Y).restrictScalars K
  rw [← tangent_derivation_constants Y hY u hu0 hker]
  change sourceVectorDerivation u (firstFiberInvariantInChart p Y hY h) = 0
  unfold firstFiberInvariantInChart
  rw [map_sub, map_sum, sourceVectorDerivation_coordinate]
  have hs : (∑ i : Fin 3, sourceVectorDerivation u
      ((coefficientPartial (K := K) Y hY i h : FractionRing (MvPolynomial (Fin 4) K)) *
        rationalCoordinate (K := K) (p i.castSucc))) =
      ∑ i : Fin 3, (coefficientPartial (K := K) Y hY i h : FractionRing (MvPolynomial (Fin 4) K)) *
        u (p i.castSucc) := by
    apply Finset.sum_congr rfl
    intro i _
    rw [(sourceVectorDerivation u).leibniz,
      tangent_derivation_kills_coefficients Y u hker,
      sourceVectorDerivation_coordinate, smul_zero, add_zero]
    rfl
  rw [hs, ← hframe, sub_self]

/-- For a nilpotent rank-three map, an independent triple in a reordered
chart gives the first invariant without an additional tangent assumption. -/
theorem firstFiberInvariantInChart_mem_of_rank_three
    (H : Fin 4 → FractionRing (MvPolynomial (Fin 4) K))
    (hN : IsNilpotent (rationalJacobian H)) (hrank : (rationalJacobian H).rank = 3)
    (p : Equiv.Perm (Fin 4))
    (hY : AlgebraicIndependent K (fun i : Fin 3 => H (p i.castSucc)))
    (h : coefficientField (K := K) (fun i : Fin 3 => H (p i.castSucc)))
    (hh : (h : FractionRing (MvPolynomial (Fin 4) K)) = H (p 3)) :
    firstFiberInvariantInChart p (fun i : Fin 3 => H (p i.castSucc)) hY h ∈
      coefficientField (K := K) (fun i : Fin 3 => H (p i.castSucc)) := by
  let Y : Fin 3 → FractionRing (MvPolynomial (Fin 4) K) := fun i => H (p i.castSucc)
  obtain ⟨u, hu0, hu⟩ := matrix_nilpotent_exists_nonzero_kernel _ hN (by omega)
  have hker : rationalJacobian Y *ᵥ u = 0 := by
    funext i
    exact congrFun hu (p i.castSucc)
  have hchart : Fin.snoc Y (h : FractionRing (MvPolynomial (Fin 4) K)) = H ∘ p := by
    funext i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · rw [Fin.snoc_last]
      change (h : FractionRing (MvPolynomial (Fin 4) K)) = H (p 3)
      exact hh
    · simp only [Fin.snoc_castSucc, Y, Function.comp_apply]
  have hnormal := fiberNormal_jacobian_zero Y hY h
  rw [hchart] at hnormal
  change fiberNormal Y hY h ᵥ* (rationalJacobian H).submatrix p id = 0 at hnormal
  rw [Matrix.submatrix_vecMul_equiv] at hnormal
  have hn : (fiberNormal Y hY h ∘ p.symm) ᵥ* rationalJacobian H = 0 := by
    simpa only [Function.comp_id] using hnormal
  have hd := matrix_nilpotent_kernel_dot_zero _ hN (by decide) (by omega)
    (fiberNormal Y hY h ∘ p.symm) u hn hu
  rw [comp_equiv_symm_dotProduct] at hd
  change (∑ i : Fin 4, fiberNormal Y hY h i * u (p i)) = 0 at hd
  rw [Fin.sum_univ_castSucc] at hd
  simp only [fiberNormal, Fin.snoc_castSucc, Fin.snoc_last, neg_mul,
    Finset.sum_neg_distrib, one_mul, fiberGradient] at hd
  have hframe : u (p 3) = ∑ i : Fin 3,
      (coefficientPartial (K := K) Y hY i h : FractionRing (MvPolynomial (Fin 4) K)) *
        u (p i.castSucc) := by
    change -(∑ i : Fin 3,
      (coefficientPartial (K := K) Y hY i h : FractionRing (MvPolynomial (Fin 4) K)) *
        u (p i.castSucc)) + u (p 3) = 0 at hd
    linear_combination hd
  exact firstFiberInvariantInChart_mem_of_frame p Y hY h u hu0 hker hframe

/-- The first invariant of Lemma 2.2 exists for every nilpotent rank-three
rational map in four variables. The independent triple, the algebraic last
output, the nonzero tangent vector and the frame identity are all derived. -/
theorem exists_firstFiberInvariant_of_nilpotent_rank_three
    (H : Fin 4 → FractionRing (MvPolynomial (Fin 4) K))
    (hN : IsNilpotent (rationalJacobian H)) (hrank : (rationalJacobian H).rank = 3) :
    ∃ (p : Equiv.Perm (Fin 4))
      (hY : AlgebraicIndependent K (fun i : Fin 3 => H (p i.castSucc)))
      (h : coefficientField (K := K) (fun i : Fin 3 => H (p i.castSucc))),
      (h : FractionRing (MvPolynomial (Fin 4) K)) = H (p 3) ∧
        firstFiberInvariantInChart p (fun i : Fin 3 => H (p i.castSucc)) hY h ∈
          coefficientField (K := K) (fun i : Fin 3 => H (p i.castSucc)) := by
  classical
  obtain ⟨s, hs, hSind, hAlg⟩ := exists_independent_output_triple H hrank
  obtain ⟨p, hp⟩ := Equiv.Perm.exists_extending_pair Fin.castSucc s (Fin.castSucc_injective 3) hs
  have hYs : (fun i : Fin 3 => H (p i.castSucc)) = fun i => H (s i) := by
    funext i
    rw [hp]
  have hY : AlgebraicIndependent K (fun i : Fin 3 => H (p i.castSucc)) := by
    rw [hYs]
    exact hSind
  have ha : IsAlgebraic
      (IntermediateField.adjoin K (Set.range (fun i : Fin 3 => H (p i.castSucc)))) (H (p 3)) := by
    rw [hYs]
    exact hAlg (p 3)
  let h : coefficientField (K := K) (fun i : Fin 3 => H (p i.castSucc)) :=
    ⟨H (p 3), mem_algebraicClosure_iff.mpr ha⟩
  exact ⟨p, hY, h, rfl, firstFiberInvariantInChart_mem_of_rank_three H hN hrank p hY h rfl⟩

/-- The first-invariant conclusion under the polynomial Jacobian and
rational-rank conventions of the paper. Homogeneity is not needed for this
part of Lemma 2.2. -/
theorem exists_firstFiberInvariant_of_polynomial_rank_three
    (H : Fin 4 → MvPolynomial (Fin 4) K) (hN : IsNilpotent (jac H))
    (hrank : polyRank (jac H) = 3) :
    let Q : Fin 4 → FractionRing (MvPolynomial (Fin 4) K) :=
      fun i => algebraMap (MvPolynomial (Fin 4) K) _ (H i)
    ∃ (p : Equiv.Perm (Fin 4))
      (hY : AlgebraicIndependent K (fun i : Fin 3 => Q (p i.castSucc)))
      (h : coefficientField (K := K) (fun i : Fin 3 => Q (p i.castSucc))),
      (h : FractionRing (MvPolynomial (Fin 4) K)) = Q (p 3) ∧
        firstFiberInvariantInChart p (fun i : Fin 3 => Q (p i.castSucc)) hY h ∈
          coefficientField (K := K) (fun i : Fin 3 => Q (p i.castSucc)) := by
  let Q : Fin 4 → FractionRing (MvPolynomial (Fin 4) K) :=
    fun i => algebraMap (MvPolynomial (Fin 4) K) _ (H i)
  have hJ : rationalJacobian Q = (jac H).map
      (algebraMap (MvPolynomial (Fin 4) K) (FractionRing (MvPolynomial (Fin 4) K))) :=
    rationalJacobian_polynomial H
  apply exists_firstFiberInvariant_of_nilpotent_rank_three Q
  · rw [hJ]
    exact hN.map (algebraMap (MvPolynomial (Fin 4) K)
      (FractionRing (MvPolynomial (Fin 4) K))).mapMatrix
  · rw [hJ]
    exact hrank

end DimensionFourDependence
