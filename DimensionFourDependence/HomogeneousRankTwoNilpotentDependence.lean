import DimensionFourDependence.IntrinsicPencilFrameContradiction
import DimensionFourDependence.PrescribedNormalizedPencilProjection

/-! # Homogeneous rank-two nilpotent maps in four variables have dependent components -/

namespace DimensionFourDependence

open Matrix MvPolynomial

universe u
set_option maxHeartbeats 5000000

variable {K : Type u} [Field K] [CharZero K] [IsAlgClosed K]
local notation "R₀" => MvPolynomial (Fin 4) K

/-- The full general-degree rank-two nilpotent dependence theorem
over algebraically closed original characteristic-zero constants.
Every source point, primitive pencil, projection equation, actual
base component, finite covector cover, avoiding frame and intrinsic
base comparison is constructed from the original map.

The proof does not assume a source pencil, primitive factorization,
classification, generic-frame condition or dependence theorem. -/
theorem closed_field_positive_homogeneous_rank_two_nilpotent_componentsDependent
    (H : Fin 4 → R₀) {d : ℕ} (hd : 0 < d) (hH : IsHomogMap H d)
    (hN : IsNilpotent (jac H)) (hrank : polyRank (jac H) = 2) :
    ComponentsDependent H := by
  by_contra hind
  obtain ⟨A, B, hAB, hBA, hGhom, hGnil, hGind, hrG, hcol0, _hcol1,
    p, q, g, D, N, c, v, hD, hNpos, hg, hpH, hqH, _hgH, _hdegree, hrel,
    hp0, hq1, _hgz, hpder, hVdeg, hprim, hfactor, _hv0, _hv01, _hv31, _hdiv0, _hdiv3, _hminor⟩ :=
    original_independent_rank_two_nilpotent_map_constructs_normalized_primitive_pencil_and_double_divisors
      H hd hH hN hrank hind
  let G := linearPolynomialConjugate A B H
  have hminors (μ ν : Fin 4 → K) (hμν : LinearIndependent K ![μ, ν]) :
      outputLinearCombination G μ * outputLinearCombination (jac G *ᵥ G) ν -
        outputLinearCombination G ν * outputLinearCombination (jac G *ᵥ G) μ ≠ 0 :=
    normalized_independent_source_pencil_covector_orbit_minor_ne_zero
      G hd hGhom hGind hcol0 p q g hg hp0 hq1 hpder v hVdeg hfactor μ ν hμν
  obtain ⟨T, S, hTS, hST, hj0, hj1, havoid⟩ :=
    nonzero_original_covector_orbit_minors_construct_normalized_frame_avoiding_pencil_base_linear_forms
      G hd hGhom hGnil hGind hminors p q
  let G' := linearPolynomialConjugate T S G
  have hG'hom : IsHomogMap G' d := linearPolynomialConjugate_homogeneous T S G hGhom
  have hG'nil : IsNilpotent (jac G') := linearPolynomialConjugate_nilpotent T S hTS hST G hGnil
  have hrG' : polyRank (jac G') = 2 := (linearPolynomialConjugate_polyRank T S hTS hST G).trans hrG
  obtain ⟨g', W', Q, α, β, hg', hprim', hfactor', hQ, hheight, hab, hlinear, hWQ⟩ :=
    normalized_homogeneous_rank_two_nilpotent_map_constructs_primitive_linear_base_prime
      G' hd hG'hom hG'nil hrG' hj0 hj1
  let : Q.IsPrime := hQ
  have hpne : p ≠ 0 := by
    intro hz
    rw [hz, map_zero, map_zero] at hpder
    exact hpder rfl
  exact intrinsic_primitive_pencil_base_frame_exclusion_forbids_fixed_plane_prime
    G p q g hD hNpos hpne hpH hqH hrel v hVdeg hprim hfactor
    T S hTS hST havoid W' g' hg' hprim' hfactor' Q hheight α β hab hlinear hWQ

end DimensionFourDependence
