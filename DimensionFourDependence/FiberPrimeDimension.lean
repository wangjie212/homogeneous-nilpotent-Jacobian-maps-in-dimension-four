import DimensionFourDependence.FiberCoordinateRing

/-! # The fiber prime is neither zero nor maximal

The nonmaximality follows from Zariski's lemma and the verified
one-variable function-field description, rather than being assumed as
part of the geometric fiber setup.
-/

namespace DimensionFourDependence

open MvPolynomial

variable {L F : Type*} [Field L] [Field F] [Algebra L F] {n : ℕ}

/-- The actual coordinate algebra is finitely generated over its coefficient field. -/
theorem fiberCoordinateAlgebra_finiteType (x : Fin n → F) :
    Algebra.FiniteType L (fiberCoordinateAlgebra (L := L) x) :=
  (inferInstance : Algebra.FiniteType L (MvPolynomial (Fin n) L ⧸ fiberVanishingIdeal (L := L) x)).equiv
    (fiberCoordinateQuotientEquiv (L := L) x)

/-- A coordinate prime whose fraction field is transcendental cannot be
maximal: a maximal quotient would be finite over the base by Zariski's lemma. -/
theorem fiberVanishingIdeal_not_isMaximal (x : Fin n → F)
    (hx : IntermediateField.adjoin L (Set.range x) = ⊤) (htr : Algebra.trdeg L F ≠ 0) :
    ¬ (fiberVanishingIdeal (L := L) x).IsMaximal := by
  intro hm
  let : (fiberVanishingIdeal (L := L) x).IsMaximal := hm
  let : Field (MvPolynomial (Fin n) L ⧸ fiberVanishingIdeal (L := L) x) :=
    Ideal.Quotient.field _
  have : Module.Finite L (MvPolynomial (Fin n) L ⧸ fiberVanishingIdeal (L := L) x) :=
    finite_of_finite_type_of_isJacobsonRing L _
  have hAlg (i : Fin n) : IsAlgebraic L (x i) := by
    have ha := IsAlgebraic.of_finite L
      (Ideal.Quotient.mk (fiberVanishingIdeal (L := L) x) (X i))
    have hb := ha.algHom (Ideal.kerLiftAlg (aeval x : MvPolynomial (Fin n) L →ₐ[L] F))
    change IsAlgebraic L ((aeval x) (X i)) at hb
    simpa only [aeval_X] using hb
  have hle : IntermediateField.adjoin L (Set.range x) ≤ algebraicClosure L F := by
    apply IntermediateField.adjoin_le_iff.mpr
    rintro _ ⟨i, rfl⟩
    exact mem_algebraicClosure_iff.mpr (hAlg i)
  rw [hx] at hle
  have : Algebra.IsAlgebraic L F := ⟨fun z => mem_algebraicClosure_iff.mp (hle (by trivial))⟩
  exact htr trdeg_eq_zero

variable {K : Type*} [Field K] [CharZero K]

/-- The actual prime relation ideal of a rank-three fiber is not maximal. -/
theorem fiber_witness_prime_not_isMaximal
    (H : Fin 4 → FractionRing (MvPolynomial (Fin 4) K))
    (hN : IsNilpotent (rationalJacobian H)) (hrank : (rationalJacobian H).rank = 3)
    (W : FiberEquationWitness H) :
    ¬ (fiberVanishingIdeal
      (L := coefficientField (K := K) (fun i : Fin 3 => H (W.chart i.castSucc)))
      (fun i : Fin 3 => rationalCoordinate (K := K) (W.chart i.castSucc))).IsMaximal := by
  apply fiberVanishingIdeal_not_isMaximal _ (fiber_witness_coordinate_field_eq_top H W)
  rw [fiber_witness_trdeg_eq_one H hN hrank W]
  exact one_ne_zero

/-- The quadratic equation gives a nonzero member of the actual prime ideal. -/
theorem fiber_witness_prime_ne_bot
    (H : Fin 4 → FractionRing (MvPolynomial (Fin 4) K)) (W : FiberEquationWitness H) :
    fiberVanishingIdeal
      (L := coefficientField (K := K) (fun i : Fin 3 => H (W.chart i.castSucc)))
      (fun i : Fin 3 => rationalCoordinate (K := K) (W.chart i.castSucc)) ≠ ⊥ := by
  intro h
  have hm := (fiber_witness_equations_mem_prime H W).1
  rw [h, Ideal.mem_bot] at hm
  exact fiber_witness_quadric_ne_zero H W hm

end DimensionFourDependence
