import DimensionFourDependence.ActualFiniteNativeRootConstruction

/-! # The original map constructs finite root forms in its native normalized pencil field -/

namespace DimensionFourDependence

open MvPolynomial

universe u

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 100000

variable {K : Type u} [Field K] [CharZero K]

/-- The original homogeneous nilpotent rank-three nonplanar map of
Gauss dimension one constructs its own finite coefficient extension and
the actual rational root n(H)L_t/m(H) in its native normalized pencil
field. Its d-th power is s(H), with a proved nonzero native denominator.
The nonzero root extends to an actual nonzero regular global section,
whose d-th power is the actual source-form section. No root, boundary,
faithful realization, coefficient compatibility or root section is supplied. -/
theorem original_nonplanar_developable_map_constructs_native_gauss_root_forms
    (H : Fin 4 → MvPolynomial (Fin 4) K) {d : ℕ} (hd : 0 < d) (hH : IsHomogMap H d)
    (hN : IsNilpotent (jac H)) (hrank : polyRank (jac H) = 3)
    (hind : ¬ ComponentsDependent H) (I : ImageRelationWitness H)
    (hGauss : gaussImageDimension H I = 1) :
    ∃ (p : Equiv.Perm (Fin 4))
      (hY : AlgebraicIndependent K (fun i : Fin 3 => algebraMap (MvPolynomial (Fin 4) K)
        (FractionRing (MvPolynomial (Fin 4) K)) (H (p i.castSucc))))
      (h : coefficientField (K := K) (fun i : Fin 3 => algebraMap (MvPolynomial (Fin 4) K)
        (FractionRing (MvPolynomial (Fin 4) K)) (H (p i.castSucc))))
      (hh : (h : FractionRing (MvPolynomial (Fin 4) K)) = algebraMap (MvPolynomial (Fin 4) K)
        (FractionRing (MvPolynomial (Fin 4) K)) (H (p 3)))
      (e : RatFunc K ≃ₐ[K] closedGaussParameterField H I),
      ActualFiniteNativeGaussRootFormsExist H I p hY h hh hH e := by
  obtain ⟨W⟩ := exists_fiber_equation_witness_polynomial H hN hrank
  obtain ⟨h, c, q, k, hh, hc, hq, hk, hc0, _hEuler, _hcEuler, _hHess⟩ :=
    developable_fiber_witness_nonzero_weighted_invariants H hd hH hN hrank hind I
      (by rw [hGauss]) W
  obtain ⟨e⟩ := actual_closed_gauss_parameter_rational_function_field H I hGauss
  have hdata := actual_gauss_boundary_root_forms_exist H hrank I W.chart W.independent h c hh e
    hd hH hN hind hGauss hc0 q k hc hq hk
  have hn := actual_closed_gauss_graph_denominator_ne_zero H I W.chart W.independent h hh e hGauss hd hH
  exact ⟨W.chart, W.independent, h, hh, e,
    actual_finite_boundary_root_forms_construct_native_root_forms H I W.chart W.independent h hh hH e
      hd c hc hc0 hdata hn⟩

end DimensionFourDependence
