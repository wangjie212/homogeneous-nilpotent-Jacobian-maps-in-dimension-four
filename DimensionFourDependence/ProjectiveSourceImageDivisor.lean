import DimensionFourDependence.ProjectiveSourceHeightOne
import Mathlib.RingTheory.Spectrum.Prime.Topology

/-! # The divisor image of a normalized chart prime

This is the actual topological image closure in the source chart's
prime spectrum. Its defining ideal is the prime's contraction. Having
an irreducible hypersurface as image is equivalent to that contraction
having height one.
-/

namespace DimensionFourDependence

open Topology

set_option synthInstance.maxHeartbeats 100000
set_option maxHeartbeats 1000000

variable {K : Type*} [Field K] (s : Fin 4 ≃ Option (Fin 3))

local notation "R₀" => projectiveCoordinateChartAlgebra (C := K)
  (rationalCoordinate (K := K) (n := 4)) (s.symm none)

variable {T : Type*} [CommRing T]

/-- The closure of the image of the closed subset defined by an
upstairs ideal, under the actual affine source spectrum morphism. -/
def projectiveSourceChartImageClosure (f : R₀ →+* T) (q : Ideal T) : Set (PrimeSpectrum R₀) :=
  closure (PrimeSpectrum.comap f '' PrimeSpectrum.zeroLocus (q : Set T))

/-- The source image closure is defined by contraction, for the
actual spectrum map rather than a stipulated image ideal. -/
theorem projective_source_chart_image_closure_eq (f : R₀ →+* T) (q : Ideal T) :
    projectiveSourceChartImageClosure s f q = PrimeSpectrum.zeroLocus (q.comap f : Set R₀) :=
  PrimeSpectrum.closure_image_comap_zeroLocus f q

/-- A prime source image is the given hypersurface precisely when
the upstairs prime contracts to that hypersurface's prime ideal. -/
theorem projective_source_chart_image_closure_eq_prime_iff (f : R₀ →+* T) (q : Ideal T) [q.IsPrime]
    (Q : Ideal R₀) [Q.IsPrime] :
    projectiveSourceChartImageClosure s f q = PrimeSpectrum.zeroLocus (Q : Set R₀) ↔
      q.comap f = Q := by
  rw [projective_source_chart_image_closure_eq, PrimeSpectrum.zeroLocus_eq_iff,
    Ideal.IsPrime.radical (inferInstance : (q.comap f).IsPrime),
    Ideal.IsPrime.radical (inferInstance : Q.IsPrime)]

/-- A source image is an irreducible affine hypersurface if and only
if the actual contracted prime has codimension one. -/
theorem projective_source_image_divisor_iff_height_one (f : R₀ →+* T) (q : Ideal T) [q.IsPrime] :
    (∃ δ : MvPolynomial (Fin 3) K, Irreducible δ ∧
      projectiveSourceChartImageClosure s f q =
        PrimeSpectrum.zeroLocus
          (Ideal.span {projectiveSourceFullChartCoordinateEquiv s δ} : Set R₀)) ↔
      (q.comap f).height = 1 := by
  constructor
  · rintro ⟨δ, hδ, himage⟩
    have hf : Prime (projectiveSourceFullChartCoordinateEquiv (K := K) s δ) :=
      (MulEquiv.prime_iff (projectiveSourceFullChartCoordinateEquiv (K := K) s)).mpr hδ.prime
    let : (Ideal.span {projectiveSourceFullChartCoordinateEquiv (K := K) s δ}).IsPrime :=
      Ideal.isPrime_span_singleton_of_prime hf
    have heq := (projective_source_chart_image_closure_eq_prime_iff s f q
      (Ideal.span {projectiveSourceFullChartCoordinateEquiv s δ})).mp himage
    let : IsNoetherianRing R₀ := projective_source_chart_isNoetherianRing s
    rw [heq]
    exact Ideal.height_span_singleton_eq_one_of_mem_nonZeroDivisors
      (mem_nonZeroDivisors_iff_ne_zero.mpr hf.ne_zero) hf.not_isUnit
  · intro hheight
    obtain ⟨δ, hδ, heq⟩ := projective_source_height_one_equation s (q.comap f) hheight
    exact ⟨δ, hδ, (projective_source_chart_image_closure_eq s f q).trans
      (congrArg (fun Q : Ideal R₀ => PrimeSpectrum.zeroLocus (Q : Set R₀)) heq)⟩

end DimensionFourDependence
