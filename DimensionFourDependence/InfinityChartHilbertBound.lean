import DimensionFourDependence.GradedProjectiveSupportTransport
import DimensionFourDependence.InvertibleInfinityChart
import DimensionFourDependence.GeometricHilbertBound
import DimensionFourDependence.HyperplaneSectionHilbertDegree
import DimensionFourDependence.FiniteGaussActualBoundaryLocalBound

/-! # The actual infinity chart bounds the original curve degree

Keep the entire coefficient-extended original closure ideal, eliminate
its infinity coordinate, and apply the constructed invertible chart.
The resulting dehomogenized ideal is exactly the original extension-valued
chart ideal. Its actual local bound therefore bounds the original Hilbert
degree as soon as a specified graded cover supplies single-point support.
-/

namespace DimensionFourDependence

open MvPolynomial Module

attribute [local instance] MvPolynomial.gradedAlgebra

variable {F sigma tau upsilon : Type*} [Field F]

/-- Composition of polynomial maps onto every homogeneous piece
is again onto every homogeneous piece. -/
theorem homogeneousPolynomialAlgebraMap_surjective_comp
    (phi : MvPolynomial sigma F →ₐ[F] MvPolynomial tau F)
    (hphi : ∀ d P, P.IsHomogeneous d → (phi P).IsHomogeneous d)
    (psi : MvPolynomial tau F →ₐ[F] MvPolynomial upsilon F)
    (hpsi : ∀ d P, P.IsHomogeneous d → (psi P).IsHomogeneous d)
    (hphiSurj : ∀ d, Function.Surjective (homogeneousPolynomialAlgebraMap phi hphi d))
    (hpsiSurj : ∀ d, Function.Surjective (homogeneousPolynomialAlgebraMap psi hpsi d)) (d : ℕ) :
    Function.Surjective (homogeneousPolynomialAlgebraMap (psi.comp phi)
      (fun d P hP => hpsi d (phi P) (hphi d P hP)) d) := by
  intro P
  obtain ⟨Q, hQ⟩ := hpsiSurj d P
  obtain ⟨R, hR⟩ := hphiSurj d Q
  refine ⟨R, ?_⟩
  apply Subtype.ext
  change psi (phi (R : MvPolynomial sigma F)) = (P : MvPolynomial upsilon F)
  have hR' : phi (R : MvPolynomial sigma F) = (Q : MvPolynomial tau F) := congrArg Subtype.val hR
  have hQ' : psi (Q : MvPolynomial tau F) = (P : MvPolynomial upsilon F) := congrArg Subtype.val hQ
  rw [hR', hQ']

/-- The actual homogeneous infinity-chart map before setting its
own chart coordinate to one. -/
noncomputable def homogeneousInfinityChartHom (b w z : Fin 3 → F)
    (hdet : (rulingBoundaryCoordinateMatrix w z b).det ≠ 0) :
    MvPolynomial (Option (Fin 3)) F →ₐ[F] MvPolynomial (Option (Fin 2)) F :=
  (homogeneousBoundaryChartEquiv b w z hdet).toAlgHom.comp projectiveInfinityCoordinateProjection

/-- This actual chart map preserves the original homogeneous degrees. -/
theorem homogeneousInfinityChartHom_homogeneous (b w z : Fin 3 → F)
    (hdet : (rulingBoundaryCoordinateMatrix w z b).det ≠ 0)
    (P : MvPolynomial (Option (Fin 3)) F) {d : ℕ} (hP : P.IsHomogeneous d) :
    (homogeneousInfinityChartHom b w z hdet P).IsHomogeneous d :=
  homogeneousBoundaryChartEquiv_homogeneous b w z hdet _
    (projectiveInfinityCoordinateProjection_homogeneous P hP)

/-- The actual chart map is onto the whole chart polynomial ring. -/
theorem homogeneousInfinityChartHom_surjective (b w z : Fin 3 → F)
    (hdet : (rulingBoundaryCoordinateMatrix w z b).det ≠ 0) :
    Function.Surjective (homogeneousInfinityChartHom b w z hdet) := by
  intro P
  refine ⟨rename some ((homogeneousBoundaryChartEquiv b w z hdet).symm P), ?_⟩
  change homogeneousBoundaryChartEquiv b w z hdet
    (projectiveInfinityCoordinateProjection (rename some
      ((homogeneousBoundaryChartEquiv b w z hdet).symm P))) = P
  rw [projectiveInfinityCoordinateProjection_rename, AlgEquiv.apply_symm_apply]

/-- The actual chart map is onto in every prescribed homogeneous degree. -/
theorem homogeneousInfinityChartHom_homogeneous_surjective (b w z : Fin 3 → F)
    (hdet : (rulingBoundaryCoordinateMatrix w z b).det ≠ 0) (d : ℕ) :
    Function.Surjective (homogeneousPolynomialAlgebraMap (homogeneousInfinityChartHom b w z hdet)
      (fun _ P hP => homogeneousInfinityChartHom_homogeneous b w z hdet P hP) d) := by
  intro P
  refine ⟨⟨rename some ((homogeneousBoundaryChartEquiv b w z hdet).symm P),
    (homogeneousBoundaryChartEquiv_symm_homogeneous b w z hdet P P.property).rename_isHomogeneous⟩, ?_⟩
  apply Subtype.ext
  change homogeneousBoundaryChartEquiv b w z hdet
    (projectiveInfinityCoordinateProjection (F := F) (sigma := Fin 3)
      (rename (some : Fin 3 → Option (Fin 3))
        ((homogeneousBoundaryChartEquiv b w z hdet).symm (P : MvPolynomial (Option (Fin 2)) F)))) = _
  rw [projectiveInfinityCoordinateProjection_rename, AlgEquiv.apply_symm_apply]

/-- The sole eliminated kernel is the original infinity coordinate. -/
theorem homogeneousInfinityChartHom_kernel (b w z : Fin 3 → F)
    (hdet : (rulingBoundaryCoordinateMatrix w z b).det ≠ 0) :
    RingHom.ker (homogeneousInfinityChartHom b w z hdet).toRingHom =
      Ideal.span ({X none} : Set (MvPolynomial (Option (Fin 3)) F)) := by
  rw [← projectiveInfinityCoordinateProjection_kernel]
  ext P
  change homogeneousBoundaryChartEquiv b w z hdet (projectiveInfinityCoordinateProjection P) = 0 ↔
    projectiveInfinityCoordinateProjection P = 0
  exact (map_eq_zero_iff (homogeneousBoundaryChartEquiv b w z hdet)
    (homogeneousBoundaryChartEquiv b w z hdet).injective)

variable {E G : Type*} [Field E] [Field G] [Algebra E F] [Algebra E G]

/-- The actual extended infinity-section ideal has precisely the
original extension-valued affine chart ideal after this substitution. -/
theorem homogeneousInfinityChartHom_dehomogenized_ideal
    (x : Fin 3 → G) (b w z : Fin 3 → F)
    (hdet : (rulingBoundaryCoordinateMatrix w z b).det ≠ 0) :
    projectiveDehomogenizedIdeal
      ((Ideal.map (MvPolynomial.map (algebraMap E F)) (projectiveConeIdeal (L := E) x) ⊔
        Ideal.span ({X none} : Set (MvPolynomial (Option (Fin 3)) F))).map
          (homogeneousInfinityChartHom b w z hdet).toRingHom) =
      extendedProjectiveInfinityChartIdeal (E := E) x b w z := by
  rw [projectiveDehomogenizedIdeal, Ideal.map_map]
  have he : (projectiveDehomogenize (R := F) (σ := Fin 2)).toRingHom.comp
      (homogeneousInfinityChartHom b w z hdet).toRingHom =
      (projectiveInfinityChartHom b w z).toRingHom :=
    congrArg AlgHom.toRingHom (homogeneousBoundaryChartEquiv_dehomogenize b w z hdet)
  rw [he, Ideal.map_sup, Ideal.map_span]
  have hx : (projectiveInfinityChartHom b w z).toRingHom (X none) = 0 := by
    simp [projectiveInfinityChartHom]
  rw [Set.image_singleton, hx, Ideal.span_singleton_zero, sup_bot_eq]
  exact (extendedProjectiveInfinityChartIdeal_eq_extended_ideal_chart x b w z).symm

/-- Extending the coefficients of the original infinity section is
exactly the extended original cone together with its infinity equation. -/
theorem extendCoefficientIdeal_infinity_section {nu : Type*} (x : nu → G) :
    extendCoefficientIdeal F (projectiveConeIdeal (L := E) x ⊔
      Ideal.span ({X none} : Set (MvPolynomial (Option nu) E))) =
      Ideal.map (MvPolynomial.map (algebraMap E F)) (projectiveConeIdeal (L := E) x) ⊔
        Ideal.span ({X none} : Set (MvPolynomial (Option nu) F)) := by
  rw [extendCoefficientIdeal, Ideal.map_sup, Ideal.map_span, Set.image_singleton, MvPolynomial.map_X]

/-- A specified graded cover with one actual projective support
point and the constructed actual local chart bound force the original
projected curve's Hilbert degree to be at most two. -/
theorem curve_hilbert_degree_le_two_of_single_support_infinity_chart
    (x : Fin 3 → G) {e : ℕ} (he : HasCurveHilbertDegree (projectiveConeIdeal (L := E) x) e)
    (I : Ideal (MvPolynomial sigma F))
    (psi : MvPolynomial sigma F →ₐ[F] MvPolynomial (Option (Fin 3)) F)
    (hpsi : ∀ d P, P.IsHomogeneous d → (psi P).IsHomogeneous d)
    (hpsiSurj : Function.Surjective psi)
    (hpsiPieces : ∀ d, Function.Surjective (homogeneousPolynomialAlgebraMap psi hpsi d))
    (himage : I.map psi.toRingHom =
      Ideal.map (MvPolynomial.map (algebraMap E F)) (projectiveConeIdeal (L := E) x) ⊔
        Ideal.span ({X none} : Set (MvPolynomial (Option (Fin 3)) F)))
    (s0 : ProjectiveSpectrum (homogeneousSubmodule sigma F))
    (hsupport : ∀ s : ProjectiveSpectrum (homogeneousSubmodule sigma F),
      I ≤ s.asHomogeneousIdeal.toIdeal → s = s0)
    (b w z : Fin 3 → F) (hdet : (rulingBoundaryCoordinateMatrix w z b).det ≠ 0)
    (hlocal : HasOriginLocalLengthAtMostTwo (extendedProjectiveInfinityChartIdeal (E := E) x b w z)) :
    e ≤ 2 := by
  let J := Ideal.map (MvPolynomial.map (algebraMap E F)) (projectiveConeIdeal (L := E) x) ⊔
    Ideal.span ({X none} : Set (MvPolynomial (Option (Fin 3)) F))
  let phi := homogeneousInfinityChartHom b w z hdet
  have hphi : ∀ d P, P.IsHomogeneous d → (phi P).IsHomogeneous d :=
    fun _ P hP => homogeneousInfinityChartHom_homogeneous b w z hdet P hP
  have hsurj := homogeneousInfinityChartHom_surjective b w z hdet
  have hpieces := homogeneousInfinityChartHom_homogeneous_surjective b w z hdet
  have hJ : J.IsHomogeneous (homogeneousSubmodule (Option (Fin 3)) F) := by
    dsimp only [J]
    rw [← extendCoefficientIdeal_infinity_section]
    exact extendCoefficientIdeal_isHomogeneous F _ (sup_coordinate_isHomogeneous _
      (projectiveConeIdeal_isHomogeneous (L := E) x) none)
  have htarget := polynomial_graded_image_ideal_isHomogeneous phi hphi J hJ
  have hchart : projectiveDehomogenizedIdeal (J.map phi.toRingHom) =
      extendedProjectiveInfinityChartIdeal (E := E) x b w z :=
    homogeneousInfinityChartHom_dehomogenized_ideal x b w z hdet
  have hlocal' : HasOriginLocalLengthAtMostTwo
      (projectiveDehomogenizedIdeal (J.map phi.toRingHom)) := hchart.symm ▸ hlocal
  obtain ⟨h0, hfin, hbound, _hlength⟩ := hlocal'
  let := hfin
  have horigin := projectiveChartOriginPoint_mem_of_dehomogenized_origin _ htarget h0
  have himage' : I.map (phi.comp psi).toRingHom = J.map phi.toRingHom := by
    change I.map (phi.toRingHom.comp psi.toRingHom) = J.map phi.toRingHom
    rw [← Ideal.map_map]
    exact congrArg (Ideal.map phi.toRingHom) himage
  have htargetSupport : ∀ s : ProjectiveSpectrum (homogeneousSubmodule (Option (Fin 2)) F),
      J.map phi.toRingHom ≤ s.asHomogeneousIdeal.toIdeal → s = projectiveChartOriginPoint := by
    have hcompPieces := homogeneousPolynomialAlgebraMap_surjective_comp psi hpsi phi hphi
      hpsiPieces hpieces
    have hsup := projective_support_single_point_of_graded_surjective_map (phi.comp psi)
      (fun d P hP => hphi d (psi P) (hpsi d P hP)) (hsurj.comp hpsiSurj)
      hcompPieces I s0 hsupport projectiveChartOriginPoint
      (by rwa [himage'])
    intro s hs
    exact hsup s (by rwa [himage'])
  obtain ⟨N, hN⟩ := projective_closure_infinity_eventual_hilbert_dimension x he
  have hvalue : ∀ n ≥ N + 1, projectiveHilbertFunction (J.map phi.toRingHom) n = e := by
    intro n hn
    have hker : RingHom.ker phi.toRingHom ≤ J := by
      change RingHom.ker (homogeneousInfinityChartHom b w z hdet).toRingHom ≤ J
      rw [homogeneousInfinityChartHom_kernel]
      exact le_sup_right
    rw [← projectiveHilbertFunction_surjective_graded_map phi hphi hsurj hpieces J hker n]
    change projectiveHilbertFunction
      (Ideal.map (MvPolynomial.map (algebraMap E F)) (projectiveConeIdeal (L := E) x) ⊔
        Ideal.span ({X none} : Set (MvPolynomial (Option (Fin 3)) F))) n = e
    rw [← extendCoefficientIdeal_infinity_section, projectiveHilbertFunction_field_extension]
    have hn' : n - 1 + 1 = n := by omega
    simpa only [hn'] using hN (n - 1) (by omega)
  exact (projective_hilbert_value_le_actual_origin_local_dimension
    (J.map phi.toRingHom) htarget h0 e (N + 1) hvalue htargetSupport).trans hbound

end DimensionFourDependence
