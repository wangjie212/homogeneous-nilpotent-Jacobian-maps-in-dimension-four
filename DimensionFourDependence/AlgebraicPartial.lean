import DimensionFourDependence.RationalPartial
import DimensionFourDependence.AlgebraicDifferential

/-! # Coordinate derivatives on an algebraic coefficient field

For every algebraic extension of `K(Y)`, these are the actual, uniquely extended
coordinate derivations used in Lemma 2.2. Their values on the coordinates
are the Kronecker symbols, and their mixed derivatives commute.
-/

namespace DimensionFourDependence

variable {K : Type*} [Field K] [CharZero K] {n : ℕ}

variable (L : Type*) [Field L] [Algebra (FractionRing (MvPolynomial (Fin n) K)) L] [Algebra K L]
  [IsScalarTower K (FractionRing (MvPolynomial (Fin n) K)) L] [Algebra.IsAlgebraic (FractionRing (MvPolynomial (Fin n) K)) L]

/-- The unique extension of a coordinate derivation from `K(Y)` to `L`. -/
noncomputable def algebraicPartial (i : Fin n) : Derivation K L L :=
  Classical.choose (existsUnique_derivation_extension_algebraic
    (K := K) (E := (FractionRing (MvPolynomial (Fin n) K))) (L := L) (rationalPartial (K := K) i))

theorem algebraicPartial_extends (i : Fin n) (a : (FractionRing (MvPolynomial (Fin n) K))) :
    algebraicPartial (K := K) L i (algebraMap (FractionRing (MvPolynomial (Fin n) K)) L a) =
      algebraMap (FractionRing (MvPolynomial (Fin n) K)) L (rationalPartial (K := K) i a) :=
  (Classical.choose_spec (existsUnique_derivation_extension_algebraic
    (K := K) (E := (FractionRing (MvPolynomial (Fin n) K))) (L := L) (rationalPartial (K := K) i))).1 a

theorem algebraicPartial_unique (i : Fin n) (D : Derivation K L L)
    (hD : ∀ a : (FractionRing (MvPolynomial (Fin n) K)), D (algebraMap (FractionRing (MvPolynomial (Fin n) K)) L a) = algebraMap (FractionRing (MvPolynomial (Fin n) K)) L (rationalPartial (K := K) i a)) :
    D = algebraicPartial (K := K) L i :=
  (Classical.choose_spec (existsUnique_derivation_extension_algebraic
    (K := K) (E := (FractionRing (MvPolynomial (Fin n) K))) (L := L) (rationalPartial (K := K) i))).2 D hD

/-- The defining delta identities for the `Y`-coordinate derivatives. -/
theorem algebraicPartial_coordinate (i j : Fin n) :
    algebraicPartial (K := K) L i (algebraMap (FractionRing (MvPolynomial (Fin n) K)) L (rationalCoordinate (K := K) j)) =
      if j = i then 1 else 0 := by
  rw [algebraicPartial_extends, rationalPartial_coordinate]
  by_cases hji : j = i <;> simp [hji]

/-- Symmetry of mixed partials after passing to the algebraic coefficient
field, as used for the tensors `D²h` and `D³h` in Lemma 2.2. -/
theorem algebraicPartials_commute (i j : Fin n) (a : L) :
    algebraicPartial (K := K) L i (algebraicPartial (K := K) L j a) =
      algebraicPartial (K := K) L j (algebraicPartial (K := K) L i a) := by
  apply derivation_extensions_commute (K := K) (E := (FractionRing (MvPolynomial (Fin n) K)))
    (rationalPartial (K := K) i) (rationalPartial (K := K) j)
  · exact algebraicPartial_extends L i
  · exact algebraicPartial_extends L j
  · exact rationalPartials_commute i j
  · intro x
    exact Algebra.IsAlgebraic.isAlgebraic x

end DimensionFourDependence
