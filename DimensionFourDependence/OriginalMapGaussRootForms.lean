import DimensionFourDependence.ActualGaussBoundaryRootConstruction

/-! # The original map constructs the finite Gauss-boundary root forms

The original nonplanar developable map supplies its chart, invariant
coefficients, boundary valuation and finite parameter extension. Thus
nc=m(Y)rho, rho^d=s(Y), s(b)=0 and the rational root formula hold in its
actual boundary coefficient extension without any assumed root data.
-/

namespace DimensionFourDependence

open MvPolynomial

universe u

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 100000

variable {K : Type u} [Field K] [CharZero K]

/-- The original homogeneous nilpotent rank-three nonplanar map of
Gauss dimension one constructs all finite root and linear-form data
of (4.4) in an actual boundary coefficient extension. No auxiliary
chart, invariant, branch, root, binary coordinate or factorization is supplied. -/
theorem original_nonplanar_developable_map_constructs_finite_gauss_root_forms
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
      c ≠ 0 ∧ ActualGaussBoundaryRootFormsExist H I p hY h c hh e d := by
  obtain ⟨W⟩ := exists_fiber_equation_witness_polynomial H hN hrank
  obtain ⟨h, c, q, k, hh, hc, hq, hk, hc0, _hEuler, _hcEuler, _hHess⟩ :=
    developable_fiber_witness_nonzero_weighted_invariants H hd hH hN hrank hind I
      (by rw [hGauss]) W
  obtain ⟨e⟩ := actual_closed_gauss_parameter_rational_function_field H I hGauss
  exact ⟨W.chart, W.independent, h, c, hh, e, hc0,
    actual_gauss_boundary_root_forms_exist H hrank I W.chart W.independent h c hh e
      hd hH hN hind hGauss hc0 q k hc hq hk⟩

end DimensionFourDependence
