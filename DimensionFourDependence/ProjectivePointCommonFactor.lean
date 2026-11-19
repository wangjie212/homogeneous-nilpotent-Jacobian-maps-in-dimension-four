import DimensionFourDependence.ProjectiveSourceHeightOne
import DimensionFourDependence.OriginalProjectiveChartRing
import DimensionFourDependence.AffineStalkDimension
import DimensionFourDependence.LocalEquivOrderTransport

/-! # Homogeneous common-factor degree from actual source-point orders

The hypotheses are orders in the actual projective source stalk, in
the standard local frame of the homogeneous sections on a coordinate open.
The affine equation and original homogeneous divisor are constructed.
-/

namespace DimensionFourDependence

open AlgebraicGeometry MvPolynomial CategoryTheory

attribute [local instance] MvPolynomial.gradedAlgebra

universe u

set_option synthInstance.maxHeartbeats 100000
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {K : Type u} [Field K]

local notation "Pₖ" => AlgebraicGeometry.Proj (homogeneousSubmodule (Fin 4) K)
local notation "R₄" => MvPolynomial (Fin 4) K

/-- Actual source-stalk section orders at a codimension-one point
force an irreducible homogeneous divisor power into the original common
factor, and hence the required lower bound on its degree. -/
theorem projective_source_point_orders_common_factor_degree
    (s : Fin 4 ≃ Option (Fin 3))
    (H P : Fin 4 → R₄) (g : R₄) {c d : ℕ}
    (hg : g ≠ 0) (hgh : g.IsHomogeneous c) (hP : IsHomogMap P d)
    (hprim : IsPrimitiveVec P) (hHP : H = fun i => g * P i)
    (x : Pₖ) (hx : x ∈ Proj.basicOpen (homogeneousSubmodule (Fin 4) K) (X (s.symm none)))
    (hcodim : Order.coheight x = 1) (a : ℕ)
    (horder : ∀ i, (Pₖ).presheaf.germ
      (Proj.basicOpen (homogeneousSubmodule (Fin 4) K) (X (s.symm none))) x hx
        ((originalProjectiveAffineSectionEquiv (K := K) (s.symm none)).symm
          (projectiveSourceSectionHom s (H i))) ∈
      (IsLocalRing.maximalIdeal ((Pₖ).presheaf.stalk x)) ^ a) :
    ∃ Δ : R₄, Irreducible Δ ∧ Δ.IsHomogeneous Δ.totalDegree ∧
      Δ ^ a ∣ g ∧ a * Δ.totalDegree ≤ g.totalDegree ∧ a ≤ g.totalDegree := by
  let U : (Pₖ).affineOpens := ⟨_, Proj.isAffineOpen_basicOpen
    (homogeneousSubmodule (Fin 4) K) (X (s.symm none))
      (isHomogeneous_X (R := K) _) (by omega)⟩
  let R := projectiveCoordinateChartAlgebra (C := K)
    (rationalCoordinate (K := K) (n := 4)) (s.symm none)
  let b := originalProjectiveAffineSectionEquiv (K := K) (s.symm none)
  let p := U.2.primeIdealOf ⟨x, hx⟩
  let Q : PrimeSpectrum R := PrimeSpectrum.comap b.symm.toRingHom p
  have hQ : p.asIdeal = Q.asIdeal.comap b.toRingHom := by
    ext r
    change r ∈ p.asIdeal ↔ b.symm (b r) ∈ p.asIdeal
    rw [b.symm_apply_apply]
  have hpheight : p.asIdeal.height = 1 := by
    have hdim : ringKrullDim ((Pₖ).presheaf.stalk x) = 1 := by
      rw [ringKrullDim_stalk_eq_coheight, hcodim]
      rfl
    have h := affineOpen_stalk_dimension_eq_prime_height (X := Pₖ) U ⟨x, hx⟩
    rw [hdim] at h
    exact_mod_cast h.symm
  have hheight : Q.asIdeal.height = 1 :=
    (b.symm.height_comap p.asIdeal).trans hpheight
  let bₓ : (Pₖ).presheaf.stalk x ≃+* Localization.AtPrime Q.asIdeal :=
    affineOpenCoordinateStalkEquiv (X := Pₖ) U (CommRingCat.of R) b ⟨x, hx⟩ Q hQ
  have hlocal : ∀ i, algebraMap R (Localization.AtPrime Q.asIdeal)
      (projectiveSourceSectionHom s (H i)) ∈
        (IsLocalRing.maximalIdeal (Localization.AtPrime Q.asIdeal)) ^ a := by
    intro i
    have hi := (local_equiv_maximalIdeal_pow_mem_iff
      (A := (Pₖ).presheaf.stalk x) (B := Localization.AtPrime Q.asIdeal) bₓ _ a).mpr (horder i)
    have hgerm := affineOpenCoordinateStalkEquiv_germ (X := Pₖ)
      U (CommRingCat.of R) b ⟨x, hx⟩ Q hQ
        (b.symm (projectiveSourceSectionHom s (H i)))
    change bₓ ((Pₖ).presheaf.germ U.1 x hx
      (b.symm (projectiveSourceSectionHom s (H i)))) = _ at hgerm
    rw [b.apply_symm_apply] at hgerm
    rwa [hgerm] at hi
  obtain ⟨δ, hδ, heq⟩ := projective_source_height_one_equation s Q.asIdeal hheight
  obtain ⟨hpow, hdeg, hsmall⟩ := projective_source_divisor_orders_common_factor_degree
    s H P g hg hgh hP hprim hHP δ hδ Q.asIdeal heq a hlocal
  have hdegree := projectiveSourceHomogeneousDivisor_totalDegree s δ hδ.ne_zero
  refine ⟨projectiveSourceHomogeneousDivisor s δ,
    projectiveSourceHomogeneousDivisor_irreducible s δ hδ, ?_, hpow, ?_, hsmall⟩
  · rw [hdegree]
    exact projectiveSourceHomogeneousDivisor_isHomogeneous s δ
  · simpa only [hdegree] using hdeg

end DimensionFourDependence
