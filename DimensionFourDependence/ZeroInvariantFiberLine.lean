import DimensionFourDependence.TwoCovectorKernel
import DimensionFourDependence.ZeroInvariantRadialCovectors
import DimensionFourDependence.FiberTangentVariation
import DimensionFourDependence.HomogeneousCoefficientEuler

/-! # The actual fiber is a line when both lower invariants vanish

This proves the `c=q=0` alternative in Section 3.2 directly in the
original source function field, using the constructed coefficient field.
-/

namespace DimensionFourDependence

open Matrix

variable {K : Type*} [Field K] [CharZero K]


section

variable (H : Fin 4 → (FractionRing (MvPolynomial (Fin 4) K))) (p : Equiv.Perm (Fin 4))
    (hY : AlgebraicIndependent K (fun i : Fin 3 => H (p i.castSucc)))


/-- In the zero-invariant branch every actual vertical tangent is a
multiple of the full output vector, including the last chart coordinate. -/
theorem zero_invariant_tangent_radial
    (hN : IsNilpotent (rationalJacobian (K := K) H)) (hrank : (rationalJacobian (K := K) H).rank = 3)
    (h : (coefficientField (K := K) (fun i : Fin 3 => H (p i.castSucc)))) (hh : (h : (FractionRing (MvPolynomial (Fin 4) K))) = H (p 3)) (hEuler : coefficientEuler (K := K) (fun i : Fin 3 => H (p i.castSucc)) hY h = h)
    (hc : firstFiberInvariantInChart (K := K) p (fun i : Fin 3 => H (p i.castSucc)) hY h = 0)
    (hq : secondFiberInvariant (K := K) p (fun i : Fin 3 => H (p i.castSucc)) hY h 0 = 0)
    (u : Fin 4 → (FractionRing (MvPolynomial (Fin 4) K))) (hu : rationalJacobian (K := K) H *ᵥ u = 0) :
    ∃ r : (FractionRing (MvPolynomial (Fin 4) K)), ∀ j, u j = r * H j := by
  let a := fiberThirdCovector (K := K) p (fun i : Fin 3 => H (p i.castSucc)) hY h 0 0
  let b := fiberSecondCovector (K := K) p (fun i : Fin 3 => H (p i.castSucc)) hY h 0
  have hc' : ((0 : (coefficientField (K := K) (fun i : Fin 3 => H (p i.castSucc)))) : (FractionRing (MvPolynomial (Fin 4) K))) = firstFiberInvariantInChart (K := K) p (fun i : Fin 3 => H (p i.castSucc)) hY h := by
    simpa only [IntermediateField.coe_zero] using hc.symm
  have hq' : ((0 : (coefficientField (K := K) (fun i : Fin 3 => H (p i.castSucc)))) : (FractionRing (MvPolynomial (Fin 4) K))) = secondFiberInvariant (K := K) p (fun i : Fin 3 => H (p i.castSucc)) hY h 0 := by
    simpa only [IntermediateField.coe_zero] using hq.symm
  have hker : rationalJacobian (K := K) (fun i : Fin 3 => H (p i.castSucc)) *ᵥ u = 0 := by
    funext i
    exact congrFun hu (p i.castSucc)
  have hab : LinearIndependent (FractionRing (MvPolynomial (Fin 4) K)) ![a, b] := by
    apply Fintype.linearIndependent_iff.mpr
    intro g hg i
    have he : g 0 • a + g 1 • b = 0 := by
      simpa only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.head_cons] using hg
    obtain ⟨h0, h1⟩ := fiber_covectors_independent H p hY h 0 0 hh hc' hq' (g 0) (g 1) he
    fin_cases i <;> assumption
  have hY0 : (fun i : Fin 3 => H (p i.castSucc)) ≠ 0 := by
    intro hz
    exact (hY.transcendental 0).ne_zero (congrFun hz 0)
  have hau : a ⬝ᵥ (fun i => u (p i.castSucc)) = 0 := by
    have hm := thirdFiberInvariant_mem_of_nilpotent_rank_three H hN hrank p hY h 0 0 hh hc' hq'
    let k : (coefficientField (K := K) (fun i : Fin 3 => H (p i.castSucc))) := ⟨thirdFiberInvariant (K := K) p (fun i : Fin 3 => H (p i.castSucc)) hY h 0 0, hm⟩
    have he := tangent_derivation_kills_coefficients (fun i : Fin 3 => H (p i.castSucc)) u hker k
    change sourceVectorDerivation u (thirdFiberInvariant (K := K) p (fun i : Fin 3 => H (p i.castSucc)) hY h 0 0) = 0 at he
    rwa [thirdFiberInvariant_deriv p (fun i : Fin 3 => H (p i.castSucc)) hY h 0 0 u hker] at he
  have hbu : b ⬝ᵥ (fun i => u (p i.castSucc)) = 0 := by
    have he := congrArg (sourceVectorDerivation u) hq
    rwa [map_zero, secondFiberInvariant_deriv p (fun i : Fin 3 => H (p i.castSucc)) hY h 0 u hker] at he
  obtain ⟨r, hr⟩ := two_covector_common_kernel a b (fun i : Fin 3 => H (p i.castSucc)) (fun i => u (p i.castSucc)) hab hY0
    (fiberThirdCovector_zero_radial p (fun i : Fin 3 => H (p i.castSucc)) hY h hEuler hq)
    (fiberSecondCovector_zero_radial p (fun i : Fin 3 => H (p i.castSucc)) hY h hEuler) hau hbu
  have hrad (i : Fin 3) : u (p i.castSucc) = r * (fun i : Fin 3 => H (p i.castSucc)) i :=
    (congrFun hr i).symm
  have hframe : u (p 3) = ∑ i : Fin 3,
      (coefficientPartial (K := K) (fun i : Fin 3 => H (p i.castSucc)) hY i h : (FractionRing (MvPolynomial (Fin 4) K))) * u (p i.castSucc) := by
    have he := congrArg (sourceVectorDerivation u) hc
    simp only [firstFiberInvariantInChart, map_sub, map_sum, map_zero,
      sourceVectorDerivation_coordinate] at he
    have hs : (∑ i : Fin 3, sourceVectorDerivation u
        ((coefficientPartial (K := K) (fun i : Fin 3 => H (p i.castSucc)) hY i h : (FractionRing (MvPolynomial (Fin 4) K))) * rationalCoordinate (K := K) (p i.castSucc))) =
        ∑ i : Fin 3, (coefficientPartial (K := K) (fun i : Fin 3 => H (p i.castSucc)) hY i h : (FractionRing (MvPolynomial (Fin 4) K))) * u (p i.castSucc) := by
      apply Finset.sum_congr rfl
      intro i _
      rw [(sourceVectorDerivation u).leibniz,
        tangent_derivation_kills_coefficients (fun i : Fin 3 => H (p i.castSucc)) u hker,
        sourceVectorDerivation_coordinate, smul_zero, add_zero]
      rfl
    rw [hs] at he
    exact sub_eq_zero.mp he
  have hsum : (∑ i : Fin 3, (coefficientPartial (K := K) (fun i : Fin 3 => H (p i.castSucc)) hY i h : (FractionRing (MvPolynomial (Fin 4) K))) * (fun i : Fin 3 => H (p i.castSucc)) i) = (h : (FractionRing (MvPolynomial (Fin 4) K))) := by
    have he := congrArg (algebraMap (coefficientField (K := K) (fun i : Fin 3 => H (p i.castSucc))) (FractionRing (MvPolynomial (Fin 4) K))) ((coefficientEuler_apply (K := K) (fun i : Fin 3 => H (p i.castSucc)) hY h).symm.trans hEuler)
    simp only [map_sum, map_mul, IntermediateField.algebraMap_apply, coefficientCoordinate_coe] at he
    calc
      _ = ∑ i : Fin 3, (fun i : Fin 3 => H (p i.castSucc)) i * (coefficientPartial (K := K) (fun i : Fin 3 => H (p i.castSucc)) hY i h : (FractionRing (MvPolynomial (Fin 4) K))) :=
        Finset.sum_congr rfl (fun i _ => mul_comm _ _)
      _ = _ := he
  refine ⟨r, ?_⟩
  intro j
  obtain ⟨k, rfl⟩ := p.surjective j
  refine Fin.lastCases ?_ (fun i => hrad i) k
  change u (p 3) = r * H (p 3)
  rw [hframe]
  simp_rw [hrad]
  calc
    _ = r * ∑ i : Fin 3, (coefficientPartial (K := K) (fun i : Fin 3 => H (p i.castSucc)) hY i h : (FractionRing (MvPolynomial (Fin 4) K))) * (fun i : Fin 3 => H (p i.castSucc)) i := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      ring
    _ = r * H (p 3) := by rw [hsum, hh]

/-- The zero-invariant case gives an actual affine line over the exact
coefficient field; no additional constant-field or tangent hypotheses remain. -/
theorem zero_invariants_imply_actual_fiber_line
    (hN : IsNilpotent (rationalJacobian (K := K) H)) (hrank : (rationalJacobian (K := K) H).rank = 3)
    (h : (coefficientField (K := K) (fun i : Fin 3 => H (p i.castSucc)))) (hh : (h : (FractionRing (MvPolynomial (Fin 4) K))) = H (p 3)) (hEuler : coefficientEuler (K := K) (fun i : Fin 3 => H (p i.castSucc)) hY h = h)
    (hc : firstFiberInvariantInChart (K := K) p (fun i : Fin 3 => H (p i.castSucc)) hY h = 0)
    (hq : secondFiberInvariant (K := K) p (fun i : Fin 3 => H (p i.castSucc)) hY h 0 = 0) :
    LiesInAffineLine (E := (coefficientField (K := K) (fun i : Fin 3 => H (p i.castSucc)))) (rationalCoordinate (K := K) (n := 4)) := by
  obtain ⟨u, hu0, hu⟩ := matrix_nilpotent_exists_nonzero_kernel _ hN (by omega)
  have hker : rationalJacobian (K := K) (fun i : Fin 3 => H (p i.castSucc)) *ᵥ u = 0 := by
    funext i
    exact congrFun hu (p i.castSucc)
  obtain ⟨r, hr⟩ := zero_invariant_tangent_radial H p hY hN hrank h hh hEuler hc hq u hu
  let v : Fin 4 → (coefficientField (K := K) (fun i : Fin 3 => H (p i.castSucc))) := fun j => (Fin.snoc (coefficientCoordinate (K := K) (fun i : Fin 3 => H (p i.castSucc))) h : Fin 4 → (coefficientField (K := K) (fun i : Fin 3 => H (p i.castSucc)))) (p.symm j)
  have hv (j : Fin 4) : algebraMap (coefficientField (K := K) (fun i : Fin 3 => H (p i.castSucc))) (FractionRing (MvPolynomial (Fin 4) K)) (v j) = H j := by
    obtain ⟨k, rfl⟩ := p.surjective j
    simp only [v, p.symm_apply_apply]
    refine Fin.lastCases ?_ (fun i => ?_) k
    · change (h : FractionRing (MvPolynomial (Fin 4) K)) = H (p 3)
      exact hh
    · simp only [Fin.snoc_castSucc, IntermediateField.algebraMap_apply, coefficientCoordinate_coe]
  apply liesInAffineLine_of_scalar_tangent_direction
    (fiberTangentDerivation (fun i : Fin 3 => H (p i.castSucc)) hY u hu0 hker) (rationalCoordinate (K := K) (n := 4))
    (fiberTangentDerivation_constant_scalar (fun i : Fin 3 => H (p i.castSucc)) hY u hu0 hker) v r
  · simpa only [fiberTangentDerivation_apply, sourceVectorDerivation_coordinate] using hu0
  · intro j
    simpa only [fiberTangentDerivation_apply, sourceVectorDerivation_coordinate, hv] using hr j


end

end DimensionFourDependence
