import DimensionFourDependence.ProjectiveSourceDivisor
import DimensionFourDependence.ProjectiveChartCommonFactor
import Mathlib.RingTheory.Ideal.UFD

/-! # Equations and local rings from codimension one on the source

A height-one prime on an actual original projective source chart
determines an irreducible polynomial equation in its three affine
coordinates. No defining equation is an additional hypothesis.
-/

namespace DimensionFourDependence

set_option synthInstance.maxHeartbeats 100000
set_option maxHeartbeats 1000000

variable {K : Type*} [Field K]

/-- Height one supplies an irreducible equation in the actual source
chart's polynomial coordinates. -/
theorem projective_source_height_one_equation
    (s : Fin 4 ≃ Option (Fin 3))
    (Q : Ideal (projectiveCoordinateChartAlgebra (C := K)
      (rationalCoordinate (K := K) (n := 4)) (s.symm none))) [Q.IsPrime]
    (hheight : Q.height = 1) :
    ∃ δ : MvPolynomial (Fin 3) K, Irreducible δ ∧
      Q = Ideal.span {projectiveSourceFullChartCoordinateEquiv s δ} := by
  let e := projectiveSourceFullChartCoordinateEquiv (K := K) s
  let p := Q.comap e.toRingHom
  have hpheight : p.height = 1 := (e.toRingEquiv.height_comap Q).trans hheight
  have hpne : p ≠ ⊥ := p.ne_bot_of_height_eq_one hpheight
  obtain ⟨δ, hδmem, hδprime⟩ := Ideal.IsPrime.exists_mem_prime_of_ne_bot
    (inferInstance : p.IsPrime) hpne
  have hp : p = Ideal.span {δ} :=
    Ideal.eq_span_singleton_of_height_eq_one hpheight hδmem hδprime
  refine ⟨δ, hδprime.irreducible, ?_⟩
  calc
    Q = (Q.comap e.toRingEquiv).map e.toRingEquiv :=
      (Q.map_comap_of_surjective e.toRingHom e.surjective).symm
    _ = (Ideal.span {δ}).map e.toRingEquiv :=
      congrArg (Ideal.map e.toRingHom) hp
    _ = _ := by rw [Ideal.map_span, Set.image_singleton]; rfl

/-- Codimension one, without a chosen equation, gives the actual source
discrete valuation ring. -/
theorem projective_source_height_one_isDVR
    (s : Fin 4 ≃ Option (Fin 3))
    (Q : Ideal (projectiveCoordinateChartAlgebra (C := K)
      (rationalCoordinate (K := K) (n := 4)) (s.symm none))) [Q.IsPrime]
    (hheight : Q.height = 1) :
    IsDiscreteValuationRing (Localization.AtPrime Q) := by
  obtain ⟨δ, hδ, hQ⟩ := projective_source_height_one_equation s Q hheight
  apply projective_source_divisor_isDVR s Q
    (projectiveSourceFullChartCoordinateEquiv s δ) _ hQ
  exact (MulEquiv.prime_iff (projectiveSourceFullChartCoordinateEquiv (K := K) s)).mpr
    hδ.prime

end DimensionFourDependence
