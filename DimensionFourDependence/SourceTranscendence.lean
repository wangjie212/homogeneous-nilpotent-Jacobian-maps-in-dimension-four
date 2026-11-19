import DimensionFourDependence.CoefficientField

/-! # Relative transcendence degree for the source and output fields

The rational source upper bound is adapted from the neighboring quartic
project's Rank2/Jacobian.lean. The relative degree bound and its application
to the actual field of constants are proved here for the present paper.
-/

namespace DimensionFourDependence

open MvPolynomial

variable {K : Type*} [Field K] {n : ℕ}

local notation "Kx" => FractionRing (MvPolynomial (Fin n) K)

theorem rationalSource_isAlgebraic_adjoin_of_coords_subset {t : Set Kx}
    (ht : Set.range (fun j : Fin n => algebraMap (MvPolynomial (Fin n) K) Kx (X j)) ⊆ t) :
    Algebra.IsAlgebraic (Algebra.adjoin K t) Kx := by
  have hsub : ∀ P : MvPolynomial (Fin n) K,
      algebraMap (MvPolynomial (Fin n) K) Kx P ∈ Algebra.adjoin K t := by
    intro P
    induction P using MvPolynomial.induction_on with
    | C a =>
      rw [← algebraMap_eq, ← IsScalarTower.algebraMap_apply K (MvPolynomial (Fin n) K) Kx]
      exact Subalgebra.algebraMap_mem _ _
    | add p q hp hq => rw [map_add]; exact Subalgebra.add_mem _ hp hq
    | mul_X p j hp =>
      rw [map_mul]
      exact Subalgebra.mul_mem _ hp (Algebra.subset_adjoin (ht ⟨j, rfl⟩))
  refine ⟨fun f => ?_⟩
  obtain ⟨P, Q, hQ, rfl⟩ := IsFractionRing.div_surjective (A := MvPolynomial (Fin n) K) f
  have hQ0 : algebraMap (MvPolynomial (Fin n) K) Kx Q ≠ 0 :=
    IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hQ
  refine ⟨Polynomial.C ⟨_, hsub Q⟩ * Polynomial.X - Polynomial.C ⟨_, hsub P⟩, ?_, ?_⟩
  · intro h
    have := congrArg (Polynomial.coeff · 1) h
    simp only [Polynomial.coeff_sub, Polynomial.coeff_C_mul_X, Polynomial.coeff_C,
      one_ne_zero, if_false, sub_zero, Polynomial.coeff_zero] at this
    exact hQ0 (congrArg Subtype.val this)
  · simp only [map_sub, map_mul, Polynomial.aeval_C, Polynomial.aeval_X]
    change algebraMap _ Kx Q * (algebraMap _ Kx P / algebraMap _ Kx Q) - algebraMap _ Kx P = 0
    rw [mul_div_cancel₀ _ hQ0, sub_self]

/-- The transcendence degree of `K(x₁, …, xₙ)` over `K` is at most `n`. (Auxiliary for the proof
of Lemma 2.1 of `quartic_dependence.pdf`.) -/
theorem rationalSource_trdeg_le : Algebra.trdeg K Kx ≤ n := by
  have := rationalSource_isAlgebraic_adjoin_of_coords_subset (K := K) (n := n) subset_rfl
  refine (Algebra.IsAlgebraic.trdeg_le_cardinalMk K
    (Set.range (fun j : Fin n => algebraMap (MvPolynomial (Fin n) K) Kx (X j)))).trans ?_
  have h := Cardinal.mk_range_le_lift
    (f := fun j : Fin n => algebraMap (MvPolynomial (Fin n) K) Kx (X j))
  simpa using h

variable {F : Type*} [Field F] [Algebra K F]

/-- In a source of transcendence degree at most `n+1`, `n` independent
outputs leave relative transcendence degree at most one. -/
theorem relative_trdeg_le_one_of_independent_outputs (Y : Fin n → F)
    (hY : AlgebraicIndependent K Y) (hF : Algebra.trdeg K F ≤ n + 1) :
    Algebra.trdeg (IntermediateField.adjoin K (Set.range Y)) F ≤ 1 := by
  let E := IntermediateField.adjoin K (Set.range Y)
  have hi : AlgebraicIndependent K (outputCoordinate (K := K) Y) := by
    apply AlgebraicIndependent.of_comp E.val
    change AlgebraicIndependent K Y
    exact hY
  have hdim : (n : Cardinal) ≤ Algebra.trdeg K E := by
    simpa using hi.lift_cardinalMk_le_trdeg
  have htower := trdeg_add_eq (A := F) K E
  have hb : (n : Cardinal) + Algebra.trdeg E F ≤ n + 1 := by
    calc
      (n : Cardinal) + Algebra.trdeg E F ≤ Algebra.trdeg K E + Algebra.trdeg E F :=
        _root_.add_le_add hdim (le_refl _)
      _ = Algebra.trdeg K F := htower
      _ ≤ n + 1 := hF
  exact (Cardinal.add_nat_le_add_nat_iff n).mp (by simpa only [add_comm] using hb)

/-- The field-of-constants assertion of Lemma 2.2 in the actual
four-variable rational source field, with three independent outputs. -/
theorem vertical_constants_rational_four [CharZero K]
    (Y : Fin 3 → FractionRing (MvPolynomial (Fin 4) K))
    (hY : AlgebraicIndependent K Y)
    (D : Derivation K (FractionRing (MvPolynomial (Fin 4) K)) (FractionRing (MvPolynomial (Fin 4) K)))
    (hD : D ≠ 0) (hDY : ∀ i, D (Y i) = 0) :
    derivationConstants D = (coefficientField (K := K) Y).restrictScalars K := by
  apply vertical_constants_eq_coefficient_field Y D hD hDY
  apply relative_trdeg_le_one_of_independent_outputs Y hY
  convert rationalSource_trdeg_le (K := K) (n := 4) using 1 <;> norm_num

end DimensionFourDependence
