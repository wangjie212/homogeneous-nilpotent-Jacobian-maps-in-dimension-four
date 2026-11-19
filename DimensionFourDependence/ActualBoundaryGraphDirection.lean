import DimensionFourDependence.ActualFullBoundaryOriginalRuling

/-! # The actual full boundary has a nonzero graph direction

The first invariant's linear graph equation determines the last original
coordinate from the first three. A nonzero full boundary direction
therefore remains nonzero in those three actual graph coordinates.
-/

namespace DimensionFourDependence

open MvPolynomial

variable {F : Type*} [Field F]

/-- A nonzero four-coordinate vector satisfying the graph relation
has nonzero first-three-coordinate projection in the same actual chart. -/
theorem nonzero_four_coordinate_graph_direction_first_three_ne_zero
    (p : Equiv.Perm (Fin 4)) (b : Fin 4 → F) (A : Fin 3 → F) (hb : b ≠ 0)
    (hlinear : b (p 3) = ∑ i : Fin 3, A i * b (p i.castSucc)) :
    (fun i : Fin 3 => b (p i.castSucc)) ≠ 0 := by
  intro hz
  have hfirst (i : Fin 3) : b (p i.castSucc) = 0 := congrFun hz i
  have hlast : b (p 3) = 0 := by rw [hlinear]; simp only [hfirst, mul_zero, Finset.sum_const_zero]
  apply hb
  funext j
  obtain ⟨i, rfl⟩ := p.surjective j
  refine Fin.lastCases ?_ (fun i => ?_) i
  · change b (p 3) = 0
    exact hlast
  · exact hfirst i

universe u

variable {K : Type u} [Field K] [CharZero K]

attribute [local instance] coefficientFieldScalarTower

set_option quotPrecheck false

/-- Every actual nonzero full-fiber boundary direction at infinity
has a nonzero three-coordinate representative in its actual graph chart. -/
theorem actual_full_fiber_boundary_first_three_direction_ne_zero
    (H : Fin 4 → MvPolynomial (Fin 4) K) (p : Equiv.Perm (Fin 4))
    (hY : AlgebraicIndependent K (fun i : Fin 3 => algebraMap (MvPolynomial (Fin 4) K)
      (FractionRing (MvPolynomial (Fin 4) K)) (H (p i.castSucc))))
    (h c : coefficientField (K := K) (fun i : Fin 3 => algebraMap (MvPolynomial (Fin 4) K)
      (FractionRing (MvPolynomial (Fin 4) K)) (H (p i.castSucc))))
    (hc : (c : FractionRing (MvPolynomial (Fin 4) K)) = firstFiberInvariantInChart p
      (fun i : Fin 3 => algebraMap (MvPolynomial (Fin 4) K) (FractionRing (MvPolynomial (Fin 4) K)) (H (p i.castSucc))) hY h)
    (κ : Type u) [Field κ]
    [Algebra (coefficientField (K := K) (fun i : Fin 3 => algebraMap (MvPolynomial (Fin 4) K)
      (FractionRing (MvPolynomial (Fin 4) K)) (H (p i.castSucc)))) κ]
    (z : Option (Fin 4) → κ) (hz : z ≠ 0) (hb : (fun i => z (some i)) ≠ 0)
    (hboundary : projectiveFieldPoint
      (E := coefficientField (K := K) (fun i : Fin 3 => algebraMap (MvPolynomial (Fin 4) K)
        (FractionRing (MvPolynomial (Fin 4) K)) (H (p i.castSucc)))) z hz ∈
      projectiveClosureSet
        (L := coefficientField (K := K) (fun i : Fin 3 => algebraMap (MvPolynomial (Fin 4) K)
          (FractionRing (MvPolynomial (Fin 4) K)) (H (p i.castSucc)))) (rationalCoordinate (K := K) (n := 4)))
    (hz0 : z none = 0) : (fun i : Fin 3 => z (some (p i.castSucc))) ≠ 0 :=
  nonzero_four_coordinate_graph_direction_first_three_ne_zero p (fun i => z (some i)) _ hb
    (actual_full_fiber_boundary_graph_linear_equation H p hY h c hc κ z hz hboundary hz0)

end DimensionFourDependence
