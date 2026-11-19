import DimensionFourDependence.InfinityCoordinateElimination
import DimensionFourDependence.ProjectiveOriginLocalHilbertBound

/-! # Transporting actual projective support into a local chart

A graded polynomial map onto every homogeneous piece pulls relevant
prime ideals back to relevant prime ideals. Surjectivity then identifies
target points from their pullbacks. Consequently a source supported at
one point is supported at the rational chart origin whenever its actual
dehomogenized ideal vanishes there. The actual Hilbert quotient comparison
therefore gives a global bound from the actual local ring.
-/

namespace DimensionFourDependence

open MvPolynomial Module

attribute [local instance] MvPolynomial.gradedAlgebra

variable {F sigma tau : Type*} [Field F]

/-- The graded ring map underlying a degree-preserving polynomial
algebra homomorphism. -/
noncomputable def gradedPolynomialAlgebraHom
    (phi : MvPolynomial sigma F →ₐ[F] MvPolynomial tau F)
    (hphi : ∀ d P, P.IsHomogeneous d → (phi P).IsHomogeneous d) :
    homogeneousSubmodule sigma F →+*ᵍ homogeneousSubmodule tau F :=
  { toRingHom := phi.toRingHom, map_mem := fun h => hphi _ _ h }

/-- A coordinate map onto every positive homogeneous piece pulls
an actual projective prime back to an actual projective prime. -/
noncomputable def projectiveGradedSurjectiveComap
    (phi : MvPolynomial sigma F →ₐ[F] MvPolynomial tau F)
    (hphi : ∀ d P, P.IsHomogeneous d → (phi P).IsHomogeneous d)
    (hpieces : ∀ d, Function.Surjective (homogeneousPolynomialAlgebraMap phi hphi d))
    (z : ProjectiveSpectrum (homogeneousSubmodule tau F)) :
    ProjectiveSpectrum (homogeneousSubmodule sigma F) where
  asHomogeneousIdeal := z.asHomogeneousIdeal.comap (gradedPolynomialAlgebraHom phi hphi)
  isPrime := by
    let := z.isPrime
    exact Ideal.comap_isPrime phi.toRingHom _
  not_irrelevant_le := by
    intro hle
    apply z.not_irrelevant_le
    apply (HomogeneousIdeal.irrelevant_le _).mpr
    intro d hd P hP
    obtain ⟨Q, hQ⟩ := hpieces d ⟨P, hP⟩
    have hm := hle (HomogeneousIdeal.mem_irrelevant_of_mem _ hd Q.property)
    change phi (Q : MvPolynomial sigma F) ∈ z.asHomogeneousIdeal at hm
    have he : phi (Q : MvPolynomial sigma F) = P := congrArg Subtype.val hQ
    exact he ▸ hm

/-- The pullback point has exactly the ordinary preimage prime ideal. -/
theorem projectiveGradedSurjectiveComap_ideal
    (phi : MvPolynomial sigma F →ₐ[F] MvPolynomial tau F)
    (hphi : ∀ d P, P.IsHomogeneous d → (phi P).IsHomogeneous d)
    (hpieces : ∀ d, Function.Surjective (homogeneousPolynomialAlgebraMap phi hphi d))
    (z : ProjectiveSpectrum (homogeneousSubmodule tau F)) :
    (projectiveGradedSurjectiveComap phi hphi hpieces z).asHomogeneousIdeal.toIdeal =
      z.asHomogeneousIdeal.toIdeal.comap phi.toRingHom := rfl

/-- A surjective graded coordinate map preserves a single actual
projective support point, with the target point specified by membership. -/
theorem projective_support_single_point_of_graded_surjective_map
    (phi : MvPolynomial sigma F →ₐ[F] MvPolynomial tau F)
    (hphi : ∀ d P, P.IsHomogeneous d → (phi P).IsHomogeneous d)
    (hsurj : Function.Surjective phi)
    (hpieces : ∀ d, Function.Surjective (homogeneousPolynomialAlgebraMap phi hphi d))
    (I : Ideal (MvPolynomial sigma F))
    (s0 : ProjectiveSpectrum (homogeneousSubmodule sigma F))
    (hsupport : ∀ s : ProjectiveSpectrum (homogeneousSubmodule sigma F),
      I ≤ s.asHomogeneousIdeal.toIdeal → s = s0)
    (z0 : ProjectiveSpectrum (homogeneousSubmodule tau F))
    (hz0 : I.map phi.toRingHom ≤ z0.asHomogeneousIdeal.toIdeal) :
    ∀ z : ProjectiveSpectrum (homogeneousSubmodule tau F),
      I.map phi.toRingHom ≤ z.asHomogeneousIdeal.toIdeal → z = z0 := by
  intro z hz
  have hp : projectiveGradedSurjectiveComap phi hphi hpieces z =
      projectiveGradedSurjectiveComap phi hphi hpieces z0 := by
    apply (hsupport _ ?_).trans (hsupport _ ?_).symm
    · exact (Ideal.map_le_iff_le_comap).mp hz
    · exact (Ideal.map_le_iff_le_comap).mp hz0
  apply ProjectiveSpectrum.ext
  apply HomogeneousIdeal.toIdeal_injective
  apply Ideal.comap_injective_of_surjective phi.toRingHom hsurj
  exact congrArg (fun s => s.asHomogeneousIdeal.toIdeal) hp

/-- Vanishing of the entire actual dehomogenized ideal at the affine
origin puts the rational projective chart origin in the actual support. -/
theorem projectiveChartOriginPoint_mem_of_dehomogenized_origin
    (I : Ideal (MvPolynomial (Option tau) F))
    (hI : I.IsHomogeneous (homogeneousSubmodule (Option tau) F))
    (hJ : projectiveDehomogenizedIdeal I ≤
      RingHom.ker (aeval (fun _ : tau => (0 : F))).toRingHom) :
    I ≤ (projectiveChartOriginPoint (F := F) (sigma := tau)).asHomogeneousIdeal.toIdeal := by
  intro P hP
  change projectiveFieldPointMap (E := F)
    (fun j : Option tau => j.elim 1 (fun _ => (0 : F))) P = 0
  apply Polynomial.ext
  intro d
  rw [projectiveFieldPointMap_coeff, Polynomial.coeff_zero]
  have hc := hJ (Ideal.mem_map_of_mem
    (projectiveDehomogenize (R := F) (σ := tau)).toRingHom
    (homogeneousComponent_mem_of_mem hI hP d))
  change aeval (fun _ : tau => (0 : F))
    (projectiveDehomogenize (homogeneousComponent d P)) = 0 at hc
  rw [aeval_projectiveDehomogenize]
  exact hc

/-- The source's actual eventual Hilbert value is bounded by the
actual origin-local dimension after a graded coordinate elimination,
provided the original projective support consists of one point. -/
theorem graded_projective_hilbert_value_le_actual_chart_local_dimension
    [Finite tau]
    (phi : MvPolynomial sigma F →ₐ[F] MvPolynomial (Option tau) F)
    (hphi : ∀ d P, P.IsHomogeneous d → (phi P).IsHomogeneous d)
    (hsurj : Function.Surjective phi)
    (hpieces : ∀ d, Function.Surjective (homogeneousPolynomialAlgebraMap phi hphi d))
    (I : Ideal (MvPolynomial sigma F))
    (hI : I.IsHomogeneous (homogeneousSubmodule sigma F))
    (hker : RingHom.ker phi.toRingHom ≤ I)
    (hJ : projectiveDehomogenizedIdeal (I.map phi.toRingHom) ≤
      RingHom.ker (aeval (fun _ : tau => (0 : F))).toRingHom)
    [Module.Finite F (Localization.AtPrime
      (zeroPointQuotientPrime (projectiveDehomogenizedIdeal (I.map phi.toRingHom)) hJ))]
    (e N : ℕ) (hN : ∀ n ≥ N, projectiveHilbertFunction I n = e)
    (s0 : ProjectiveSpectrum (homogeneousSubmodule sigma F))
    (hsupport : ∀ s : ProjectiveSpectrum (homogeneousSubmodule sigma F),
      I ≤ s.asHomogeneousIdeal.toIdeal → s = s0) :
    e ≤ finrank F (Localization.AtPrime
      (zeroPointQuotientPrime (projectiveDehomogenizedIdeal (I.map phi.toRingHom)) hJ)) := by
  have htarget := polynomial_graded_image_ideal_isHomogeneous phi hphi I hI
  apply projective_hilbert_value_le_actual_origin_local_dimension
    (I.map phi.toRingHom) htarget hJ e N
  · intro n hn
    rw [← projectiveHilbertFunction_surjective_graded_map phi hphi hsurj hpieces I hker n]
    exact hN n hn
  · exact projective_support_single_point_of_graded_surjective_map phi hphi hsurj hpieces I
      s0 hsupport projectiveChartOriginPoint
      (projectiveChartOriginPoint_mem_of_dehomogenized_origin _ htarget hJ)

end DimensionFourDependence
