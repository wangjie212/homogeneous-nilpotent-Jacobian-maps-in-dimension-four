import DimensionFourDependence.AffineHyperplane
import DimensionFourDependence.CoefficientCurveField

/-! # The projected fiber generates the original source function field -/

namespace DimensionFourDependence

open MvPolynomial

variable {K : Type*} [Field K] {n : ℕ}

/-- An intermediate field containing all rational source coordinates is
the whole rational function field. -/
theorem rationalSource_field_eq_top_of_coordinates
    (E : IntermediateField K (FractionRing (MvPolynomial (Fin n) K)))
    (hX : ∀ i, rationalCoordinate (K := K) i ∈ E) : E = ⊤ := by
  have hpoly (P : MvPolynomial (Fin n) K) :
      algebraMap (MvPolynomial (Fin n) K) (FractionRing (MvPolynomial (Fin n) K)) P ∈ E := by
    induction P using MvPolynomial.induction_on with
    | C a =>
      rw [← algebraMap_eq, ← IsScalarTower.algebraMap_apply K (MvPolynomial (Fin n) K)
        (FractionRing (MvPolynomial (Fin n) K))]
      exact E.algebraMap_mem a
    | add p q hp hq => rw [map_add]; exact E.add_mem hp hq
    | mul_X p i hp => rw [map_mul]; exact E.mul_mem hp (hX i)
  apply top_unique
  intro f _
  obtain ⟨P, Q, _, rfl⟩ := IsFractionRing.div_surjective (A := MvPolynomial (Fin n) K) f
  exact E.div_mem (hpoly P) (hpoly Q)

variable {E : Type*} [Field E] [Algebra K E]
  [Algebra E (FractionRing (MvPolynomial (Fin 4) K))]
  [IsScalarTower K E (FractionRing (MvPolynomial (Fin 4) K))]

/-- A graph hyperplane over `E` makes the first three reordered source
coordinates generate the full source field over `E`. -/
theorem rationalSource_adjoin_three_eq_top_of_hyperplane
    (p : Equiv.Perm (Fin 4)) (P : MvPolynomial (Fin 4) E)
    (hP : P.totalDegree ≤ 1) (hlast : pderiv (Fin.last 3) P = 1)
    (hzero : aeval (fun i => rationalCoordinate (K := K) (p i)) P = 0) :
    IntermediateField.adjoin E (Set.range (fun i : Fin 3 => rationalCoordinate (K := K) (p i.castSucc))) = ⊤ := by
  let M := IntermediateField.adjoin E
    (Set.range (fun i : Fin 3 => rationalCoordinate (K := K) (p i.castSucc)))
  have hlastmem : rationalCoordinate (K := K) (p (Fin.last 3)) ∈ M :=
    affine_hyperplane_last_mem_adjoin P hP hlast
      (fun i => rationalCoordinate (K := K) (p i)) hzero
  have hcoords : ∀ j, rationalCoordinate (K := K) j ∈ M.restrictScalars K := by
    intro j
    rw [← p.apply_symm_apply j]
    refine Fin.lastCases ?_ (fun i => ?_) (p.symm j)
    · exact hlastmem
    · exact IntermediateField.subset_adjoin E _ ⟨i, rfl⟩
  have htop := rationalSource_field_eq_top_of_coordinates (M.restrictScalars K) hcoords
  apply top_unique
  intro f _
  change f ∈ M
  have hm : f ∈ M.restrictScalars K := by rw [htop]; trivial
  exact hm

variable [CharZero K]

omit [CharZero K] in
/-- The three coordinates used by every fiber witness generate its
source function field over the actual coefficient field. -/
theorem fiber_witness_coordinate_field_eq_top
    (H : Fin 4 → FractionRing (MvPolynomial (Fin 4) K)) (W : FiberEquationWitness H) :
    IntermediateField.adjoin (coefficientField (K := K) (fun i : Fin 3 => H (W.chart i.castSucc)))
      (Set.range (fun i : Fin 3 => rationalCoordinate (K := K) (W.chart i.castSucc))) = ⊤ := by
  let : IsScalarTower K
      (coefficientField (K := K) (fun i : Fin 3 => H (W.chart i.castSucc)))
      (FractionRing (MvPolynomial (Fin 4) K)) := coefficientFieldScalarTower _
  exact rationalSource_adjoin_three_eq_top_of_hyperplane W.chart W.hyperplane
    W.hyperplane_degree W.hyperplane_last_derivative W.hyperplane_zero

end DimensionFourDependence
