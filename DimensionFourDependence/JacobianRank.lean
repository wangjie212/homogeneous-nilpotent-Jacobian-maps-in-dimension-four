import DimensionFourDependence.FiberJacobian

/-! # Relating the output field and the rational Jacobian rank

The chain rule bounds the Jacobian rank by the number of independent output
generators. In the square case, an independent output family is a
transcendence basis of the source field and has full Jacobian rank.
-/

namespace DimensionFourDependence

open Matrix

variable {K : Type*} [Field K] [CharZero K] {n m r : ℕ}

/-- The algebraic chain rule as a rectangular matrix factorization. -/
theorem coefficient_jacobian_factorization
    (Y : Fin n → FractionRing (MvPolynomial (Fin r) K)) (hY : AlgebraicIndependent K Y)
    (H : Fin m → coefficientField (K := K) Y) :
    rationalJacobian (fun i => (H i : FractionRing (MvPolynomial (Fin r) K))) =
      Matrix.of (fun i j => (coefficientPartial (K := K) Y hY j (H i) :
        FractionRing (MvPolynomial (Fin r) K))) * rationalJacobian Y := by
  ext i j
  rw [Matrix.mul_apply]
  change rationalPartial (K := K) j (H i : FractionRing (MvPolynomial (Fin r) K)) = _
  rw [coefficient_chain_rule Y hY]
  simp only [Matrix.of_apply, rationalJacobian, mul_comm]

/-- If all outputs are algebraic over `K(Y)`, their Jacobian rank is
bounded by the number of coordinates in `Y`. -/
theorem rationalJacobian_rank_le_of_algebraic_outputs
    (Y : Fin n → FractionRing (MvPolynomial (Fin r) K)) (hY : AlgebraicIndependent K Y)
    (H : Fin m → FractionRing (MvPolynomial (Fin r) K))
    (hH : ∀ i, IsAlgebraic (IntermediateField.adjoin K (Set.range Y)) (H i)) :
    (rationalJacobian H).rank ≤ n := by
  let A : Fin m → coefficientField (K := K) Y :=
    fun i => ⟨H i, mem_algebraicClosure_iff.mpr (hH i)⟩
  have hfac := coefficient_jacobian_factorization Y hY A
  change rationalJacobian H = _ at hfac
  rw [hfac]
  exact (Matrix.rank_mul_le_left _ _).trans (Matrix.rank_le_width _)

/-- An independent square output family has full rational Jacobian rank
in characteristic zero. -/
theorem rationalJacobian_rank_of_square_independent
    (Y : Fin n → FractionRing (MvPolynomial (Fin n) K)) (hY : AlgebraicIndependent K Y) :
    (rationalJacobian Y).rank = n := by
  have hb := hY.isTranscendenceBasis_of_lift_trdeg_le_of_finite
    (by simpa using rationalSource_trdeg_le (K := K) (n := n))
  have hAlg (x : FractionRing (MvPolynomial (Fin n) K)) :
      IsAlgebraic (IntermediateField.adjoin K (Set.range Y)) x :=
    IntermediateField.isAlgebraic_adjoin_iff.mpr (hb.isAlgebraic.isAlgebraic x)
  let x : Fin n → coefficientField (K := K) Y := fun j =>
    ⟨rationalCoordinate (K := K) j, mem_algebraicClosure_iff.mpr (hAlg _)⟩
  let G : Matrix (Fin n) (Fin n) (FractionRing (MvPolynomial (Fin n) K)) :=
    Matrix.of fun i j => (coefficientPartial (K := K) Y hY i (x j) :
      FractionRing (MvPolynomial (Fin n) K))
  have hid : (rationalJacobian Y)ᵀ * G = 1 := by
    ext j k
    rw [Matrix.mul_apply, Matrix.one_apply]
    change (∑ i : Fin n, rationalPartial (K := K) j (Y i) *
      (coefficientPartial (K := K) Y hY i (x k) : FractionRing (MvPolynomial (Fin n) K))) = _
    rw [← coefficient_chain_rule Y hY]
    change rationalPartial (K := K) j (rationalCoordinate (K := K) k) = _
    rw [rationalPartial_coordinate]
    simp only [eq_comm]
  have hle : n ≤ (rationalJacobian Y)ᵀ.rank := by
    calc
      n = (1 : Matrix (Fin n) (Fin n) (FractionRing (MvPolynomial (Fin n) K))).rank := by simp
      _ = ((rationalJacobian Y)ᵀ * G).rank := congrArg Matrix.rank hid.symm
      _ ≤ (rationalJacobian Y)ᵀ.rank := Matrix.rank_mul_le_left _ _
  have hle' : n ≤ (rationalJacobian Y).rank := by simpa only [Matrix.rank_transpose] using hle
  exact Nat.le_antisymm (Matrix.rank_le_width _) hle'

/-- Rank three rules out independence of all four output coordinates. -/
theorem not_independent_of_jacobian_rank_three
    (H : Fin 4 → FractionRing (MvPolynomial (Fin 4) K))
    (hrank : (rationalJacobian H).rank = 3) : ¬ AlgebraicIndependent K H := by
  intro hH
  have hfull := rationalJacobian_rank_of_square_independent H hH
  omega

end DimensionFourDependence
