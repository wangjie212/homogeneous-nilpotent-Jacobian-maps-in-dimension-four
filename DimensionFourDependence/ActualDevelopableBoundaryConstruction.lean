import DimensionFourDependence.ActualDevelopableBoundaryWitness

/-! # Boundary data constructed from the original nonplanar developable map -/

namespace DimensionFourDependence

open MvPolynomial Matrix

universe u

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 100000

variable {K : Type u} [Field K] [CharZero K]

/-- The original homogeneous nilpotent rank-three nonplanar map
constructs its own independent graph chart, nonzero first invariant,
closed Gauss cover, valuation and actual nonzero projective boundary
direction satisfying the ruling and modified quadratic equations.
No chart, coefficient, parameter presentation or boundary point is given.
Algebraicity over the Gauss parameter alone is a remaining obligation. -/
theorem actual_nonplanar_developable_map_has_boundary_direction
    (H : Fin 4 → MvPolynomial (Fin 4) K) {d : ℕ} (hd : 0 < d) (hH : IsHomogMap H d)
    (hN : IsNilpotent (jac H)) (hrank : polyRank (jac H) = 3)
    (hind : ¬ ComponentsDependent H) (I : ImageRelationWitness H)
    (hGauss : gaussImageDimension H I = 1) :
    ∃ (p : Equiv.Perm (Fin 4))
      (hY : AlgebraicIndependent K (fun i : Fin 3 => algebraMap (MvPolynomial (Fin 4) K)
        (FractionRing (MvPolynomial (Fin 4) K)) (H (p i.castSucc))))
      (h c : coefficientField (K := K) (fun i : Fin 3 => algebraMap (MvPolynomial (Fin 4) K)
        (FractionRing (MvPolynomial (Fin 4) K)) (H (p i.castSucc))))
      (hh : (h : FractionRing (MvPolynomial (Fin 4) K)) = algebraMap (MvPolynomial (Fin 4) K)
        (FractionRing (MvPolynomial (Fin 4) K)) (H (p 3)))
      (e : RatFunc K ≃ₐ[K] closedGaussParameterField H I),
      c ≠ 0 ∧ ActualClosedGaussBoundaryDirectionExists H I p hY h c hh e := by
  obtain ⟨W⟩ := exists_fiber_equation_witness_polynomial H hN hrank
  obtain ⟨h, c, q, k, hh, hc, hq, hk, hc0, _hEuler, _hcEuler, _hHess⟩ :=
    developable_fiber_witness_nonzero_weighted_invariants H hd hH hN hrank hind I
      (by rw [hGauss]) W
  obtain ⟨e⟩ := actual_closed_gauss_parameter_rational_function_field H I hGauss
  refine ⟨W.chart, W.independent, h, c, hh, e, hc0, ?_⟩
  exact actual_closed_gauss_boundary_direction_exists H I W.chart W.independent h c hh e
    hd hH hN hrank hGauss q k hc hq hk

end DimensionFourDependence
