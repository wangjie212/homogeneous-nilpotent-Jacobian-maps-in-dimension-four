import DimensionFourDependence.ActualFiniteGaussBoundaryConstruction

/-! # The original nonplanar developable map supplies its finite boundary branch

All charts, invariant coefficients, rational parameters and boundary
data are constructed from the original homogeneous nilpotent map.
The branch is algebraic over the original Gauss parameter itself and
satisfies the actual zero acceleration equation with nonzero nc.
-/

namespace DimensionFourDependence

open MvPolynomial

universe u

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 100000

variable {K : Type u} [Field K] [CharZero K]

/-- The original homogeneous nilpotent rank-three nonplanar map of
Gauss dimension one constructs its own independent graph chart, nonzero
first invariant, closed Gauss parameter, actual full-coordinate boundary,
finite original Gauss-field ruling branch and zero acceleration. -/
theorem original_nonplanar_developable_map_has_finite_gauss_boundary_branch
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
      c ≠ 0 ∧ ActualFiniteGaussBoundaryDirectionExists H hrank I p hY h c hh e := by
  obtain ⟨W⟩ := exists_fiber_equation_witness_polynomial H hN hrank
  obtain ⟨h, c, q, k, hh, hc, hq, hk, hc0, _hEuler, _hcEuler, _hHess⟩ :=
    developable_fiber_witness_nonzero_weighted_invariants H hd hH hN hrank hind I
      (by rw [hGauss]) W
  obtain ⟨e⟩ := actual_closed_gauss_parameter_rational_function_field H I hGauss
  exact ⟨W.chart, W.independent, h, c, hh, e, hc0,
    actual_finite_gauss_boundary_direction_exists H hrank I W.chart W.independent h c hh e
      hd hH hN hind hGauss q k hc hq hk⟩

end DimensionFourDependence
