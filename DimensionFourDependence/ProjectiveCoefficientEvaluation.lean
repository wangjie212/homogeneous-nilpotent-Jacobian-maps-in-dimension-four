import DimensionFourDependence.ExtendedGaussProjectiveSections

/-! # Coordinate compatibility determines projective coefficient pullback -/

namespace DimensionFourDependence

open MvPolynomial HomogeneousLocalization AlgebraicGeometry CategoryTheory

attribute [local instance] MvPolynomial.gradedAlgebra

universe u

set_option synthInstance.maxHeartbeats 100000
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

variable {C E F G : Type u} [Field C] [Field E] [Field F] [Field G]
  [Algebra C F] [Algebra E G] (f : C →+* E)
  (x : Fin 4 → F) (y : Fin 4 → G) (a : Fin 4)

local notation "S" => projectiveCoordinateChartAlgebra (C := C) x a
local notation "T" => projectiveCoordinateChartAlgebra (C := E) y a

/-- Coefficient and ratio compatibility determines every polynomial
value in a projective coordinate chart. -/
theorem projective_chart_coefficient_aeval (φ : S →+* T)
    (hc : ∀ c : C, φ (algebraMap C S c) = algebraMap E T (f c))
    (hx : ∀ i : Fin 4, φ (projectiveChartTransition (C := C) x a i) =
      projectiveChartTransition (C := E) y a i)
    (P : MvPolynomial (Fin 4) C) :
    φ (aeval (fun i => projectiveChartTransition (C := C) x a i) P) =
      MvPolynomial.eval₂Hom ((algebraMap E T).comp f)
        (fun i => projectiveChartTransition (C := E) y a i) P := by
  let ν := MvPolynomial.eval₂Hom ((algebraMap E T).comp f)
    (fun i => projectiveChartTransition (C := E) y a i)
  have h : φ.comp (aeval (fun i => projectiveChartTransition (C := C) x a i)).toRingHom = ν := by
    apply MvPolynomial.ringHom_ext
    · intro c
      change φ (aeval (fun i => projectiveChartTransition (C := C) x a i) (MvPolynomial.C c)) = ν (MvPolynomial.C c)
      simp only [ν, aeval_C, eval₂Hom_C, RingHom.comp_apply]
      exact hc c
    · intro i
      change φ (aeval (fun i => projectiveChartTransition (C := C) x a i) (X i)) = ν (X i)
      simp only [ν, aeval_X, eval₂Hom_X']
      exact hx i
  exact RingHom.congr_fun h P

/-- Coordinate compatibility also determines every homogeneous
fraction in the actual projective chart localization. -/
theorem projective_chart_coefficient_homogeneous_fraction
    (φ : S →+* T)
    (hc : ∀ c : C, φ (algebraMap C S c) = algebraMap E T (f c))
    (hx : ∀ i : Fin 4, φ (projectiveChartTransition (C := C) x a i) =
      projectiveChartTransition (C := E) y a i)
    (ha : x a ≠ 0) (hb : y a ≠ 0)
    (w : Away (homogeneousSubmodule (Fin 4) C) (X a)) :
    φ (homogeneousCoordinateChartToSource (C := C) x a ha w) =
      homogeneousCoordinateChartToSource (C := E) y a hb (polynomialCoefficientAwayHom f a w) := by
  obtain ⟨n, P, hP, rfl⟩ := Away.mk_surjective (homogeneousSubmodule (Fin 4) C)
    (isHomogeneous_X (R := C) a) w
  have horig : homogeneousCoordinateChartToSource (C := C) x a ha
      (Away.mk _ (isHomogeneous_X (R := C) _) n P hP) =
      aeval (fun i => projectiveChartTransition (C := C) x a i) P := by
    apply Subtype.ext
    change homogeneousCoordinateChartEval x a ha _ = _
    rw [homogeneousCoordinateChartEval_mk_normalized]
    exact (MvPolynomial.comp_aeval_apply
      (fun i => projectiveChartTransition (C := C) x a i) (S).val P).symm
  rw [polynomialCoefficientAwayHom_mk, horig, projective_chart_coefficient_aeval f x y a φ hc hx]
  apply Subtype.ext
  change ((T).val.toRingHom.comp (MvPolynomial.eval₂Hom ((algebraMap E T).comp f)
      (fun i => projectiveChartTransition (C := E) y a i))) P = homogeneousCoordinateChartEval y a hb _
  have hmap : (T).val.toRingHom.comp (MvPolynomial.eval₂Hom ((algebraMap E T).comp f)
        (fun i => projectiveChartTransition (C := E) y a i)) =
      (aeval (fun i => y i / y a)).toRingHom.comp (MvPolynomial.map f) := by
    apply MvPolynomial.ringHom_ext
    · intro c
      simp only [RingHom.comp_apply, eval₂Hom_C, MvPolynomial.map_C,
        AlgHom.toRingHom_eq_coe, RingHom.coe_coe, aeval_C]
      rfl
    · intro i
      simp only [RingHom.comp_apply, eval₂Hom_X', MvPolynomial.map_X,
        AlgHom.toRingHom_eq_coe, RingHom.coe_coe, aeval_X]
      rfl
  exact (RingHom.congr_fun hmap P).trans
    (homogeneousCoordinateChartEval_mk_normalized y a hb n
      (MvPolynomial.map f P) (hP.map f)).symm

/-- The actual geometric coefficient pullback on projective sections
is determined by its values on coefficients and coordinate ratios. -/
theorem projective_ambient_coefficient_section_compatibility
    (φ : S →+* T)
    (hc : ∀ c : C, φ (algebraMap C S c) = algebraMap E T (f c))
    (hx : ∀ i : Fin 4, φ (projectiveChartTransition (C := C) x a i) =
      projectiveChartTransition (C := E) y a i)
    (ha : x a ≠ 0) (hb : y a ≠ 0)
    (r : Γ(AlgebraicGeometry.Proj (homogeneousSubmodule (Fin 4) C),
      Proj.basicOpen (homogeneousSubmodule (Fin 4) C) (X a))) :
    projectiveAmbientSectionToSource (C := E) y a hb
        ((polynomialProjectiveCoefficientMap f).appLE _ _
          (le_of_eq (polynomialProjectiveCoefficientMap_preimage_basicOpen f a).symm) r) =
      φ (projectiveAmbientSectionToSource (C := C) x a ha r) := by
  let kIso := Proj.basicOpenIsoAway (homogeneousSubmodule (Fin 4) C) (X a)
    (isHomogeneous_X (R := C) a) (by omega)
  obtain ⟨w, rfl⟩ := kIso.commRingCatIsoToRingEquiv.surjective r
  have hs := ConcreteCategory.congr_hom (polynomialProjectiveCoefficientMap_awayToSection f a) w
  change (polynomialProjectiveCoefficientMap f).appLE _ _ _ (kIso.hom w) =
    (Proj.basicOpenIsoAway (homogeneousSubmodule (Fin 4) E) (X a)
      (isHomogeneous_X (R := E) a) (by omega)).hom (polynomialCoefficientAwayHom f a w) at hs
  rw [show kIso.commRingCatIsoToRingEquiv w = kIso.hom w from rfl]
  rw [hs, projectiveAmbientSectionToSource_awayToSection, projectiveAmbientSectionToSource_awayToSection]
  exact (projective_chart_coefficient_homogeneous_fraction f x y a φ hc hx ha hb w).symm

end DimensionFourDependence
