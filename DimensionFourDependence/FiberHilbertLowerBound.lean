import DimensionFourDependence.HilbertPolynomialBounds

/-! # The fiber Hilbert polynomial cannot be constant

A transcendental source coordinate gives `n+1` independent homogeneous
sections in degree `n`. Such a coordinate exists because the actual fiber
function field has relative transcendence degree one.
-/

namespace DimensionFourDependence

open MvPolynomial Module

variable {L F σ : Type*} [Field L] [Field F] [Algebra L F]

/-- Evaluation on the affine chart descends to each homogeneous quotient piece. -/
noncomputable def projectiveChartQuotientMap (x : σ → F) (d : ℕ) :
    ((homogeneousSubmodule (Option σ) L d) ⧸
      homogeneousRelationSpace (projectiveConeIdeal (L := L) x) d) →ₗ[L] F := by
  let E := (aeval (fun j : Option σ => j.elim 1 x)).toLinearMap.comp
    (homogeneousSubmodule (Option σ) L d).subtype
  apply (homogeneousRelationSpace (projectiveConeIdeal (L := L) x) d).liftQ E
  intro p hp
  change aeval (fun j : Option σ => j.elim 1 x) (p : MvPolynomial (Option σ) L) = 0
  exact (projectiveConeIdeal_mem_of_isHomogeneous x p.property).mp hp

theorem projectiveChartQuotientMap_mk (x : σ → F) (d : ℕ)
    (p : homogeneousSubmodule (Option σ) L d) :
    projectiveChartQuotientMap (L := L) x d
      ((homogeneousRelationSpace (projectiveConeIdeal (L := L) x) d).mkQ p) =
        aeval (fun j : Option σ => j.elim 1 x) (p : MvPolynomial (Option σ) L) := rfl

/-- The degree-`n` section that evaluates to the `k`-th power of a chosen coordinate. -/
noncomputable def projectiveCoordinatePower (i : σ) (n : ℕ) (k : Fin (n + 1)) :
    homogeneousSubmodule (Option σ) L n :=
  ⟨X (some i) ^ (k : ℕ) * X none ^ (n - k), by
    change (X (some i) ^ (k : ℕ) * X none ^ (n - k) : MvPolynomial (Option σ) L).IsHomogeneous n
    have hh := (isHomogeneous_X_pow (R := L) (some i) (k : ℕ)).mul
      (isHomogeneous_X_pow (R := L) none (n - k))
    convert hh using 1
    omega⟩

theorem projectiveChartQuotientMap_coordinatePower (x : σ → F) (i : σ) (n : ℕ) (k : Fin (n + 1)) :
    projectiveChartQuotientMap (L := L) x n
      ((homogeneousRelationSpace (projectiveConeIdeal (L := L) x) n).mkQ
        (projectiveCoordinatePower (L := L) i n k)) = x i ^ (k : ℕ) := by
  rw [projectiveChartQuotientMap_mk]
  simp [projectiveCoordinatePower]

/-- A transcendental coordinate supplies `n+1` independent sections in degree `n`. -/
theorem projectiveConeIdeal_hilbert_lower_bound [Finite σ]
    (x : σ → F) (i : σ) (hi : Transcendental L (x i)) (n : ℕ) :
    n + 1 ≤ projectiveHilbertFunction (projectiveConeIdeal (L := L) x) n := by
  have hpow : LinearIndependent L (fun k : ℕ => x i ^ k) := by
    have h := (Polynomial.basisMonomials L).linearIndependent.map'
      (Polynomial.aeval (x i)).toLinearMap (LinearMap.ker_eq_bot.mpr (transcendental_iff_injective.mp hi))
    simpa [Function.comp_def, Polynomial.coe_basisMonomials, Polynomial.aeval_monomial] using h
  let v := fun k : Fin (n + 1) =>
    (homogeneousRelationSpace (projectiveConeIdeal (L := L) x) n).mkQ
      (projectiveCoordinatePower (L := L) i n k)
  have hv : LinearIndependent L v := by
    apply LinearIndependent.of_comp (projectiveChartQuotientMap (L := L) x n)
    simpa only [Function.comp_def, v, projectiveChartQuotientMap_coordinatePower] using
      hpow.comp (fun k : Fin (n + 1) => (k : ℕ)) Fin.val_injective
  simpa only [Fintype.card_fin, projectiveHilbertFunction] using hv.fintype_card_le_finrank

/-- Coordinates generating a transcendental extension cannot all be algebraic. -/
theorem exists_transcendental_coordinate (x : σ → F)
    (hx : IntermediateField.adjoin L (Set.range x) = ⊤) (htr : Algebra.trdeg L F ≠ 0) :
    ∃ i : σ, Transcendental L (x i) := by
  by_contra hnone
  have hAlg (i : σ) : IsAlgebraic L (x i) := by
    by_contra hi
    exact hnone ⟨i, hi⟩
  have hle : IntermediateField.adjoin L (Set.range x) ≤ algebraicClosure L F := by
    apply IntermediateField.adjoin_le_iff.mpr
    rintro _ ⟨i, rfl⟩
    exact mem_algebraicClosure_iff.mpr (hAlg i)
  rw [hx] at hle
  have : Algebra.IsAlgebraic L F := ⟨fun z => mem_algebraicClosure_iff.mp (hle (by trivial))⟩
  exact htr trdeg_eq_zero

variable {K : Type*} [Field K] [CharZero K]

/-- The actual generic projective fiber has Hilbert function at least `n+1`. -/
theorem projective_fiber_witness_hilbert_lower_bound
    (H : Fin 4 → FractionRing (MvPolynomial (Fin 4) K))
    (hN : IsNilpotent (rationalJacobian H)) (hrank : (rationalJacobian H).rank = 3)
    (W : ProjectiveFiberEquationWitness H) (n : ℕ) :
    n + 1 ≤ projectiveHilbertFunction (projectiveConeIdeal
      (L := coefficientField (K := K) (fun i : Fin 3 => H (W.affine.chart i.castSucc)))
      (fun i : Fin 3 => rationalCoordinate (K := K) (W.affine.chart i.castSucc))) n := by
  obtain ⟨i, hi⟩ := exists_transcendental_coordinate
    (L := coefficientField (K := K) (fun i : Fin 3 => H (W.affine.chart i.castSucc)))
    (fun i : Fin 3 => rationalCoordinate (K := K) (W.affine.chart i.castSucc))
    (fiber_witness_coordinate_field_eq_top H W.affine.toFiberEquationWitness)
    (by rw [fiber_witness_trdeg_eq_one H hN hrank W.affine.toFiberEquationWitness]; exact one_ne_zero)
  exact projectiveConeIdeal_hilbert_lower_bound _ i hi n

end DimensionFourDependence
