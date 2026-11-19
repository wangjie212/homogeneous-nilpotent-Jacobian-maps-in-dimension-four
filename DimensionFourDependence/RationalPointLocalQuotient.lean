import DimensionFourDependence.RationalPointLocalModel

/-! # Canonical surjective local maps for subschemes through a rational point

Containing the original polynomial equations gives a canonical map
between the two quotient rings. Both origin evaluations agree, so
the map extends to their actual origin localizations. Lifting the
numerator and denominator of an arbitrary local fraction proves that
this canonical local map is surjective.
-/

namespace DimensionFourDependence

open MvPolynomial

variable {F sigma : Type*} [Field F]
    (J I : Ideal (MvPolynomial sigma F))
    (hJ : J ≤ RingHom.ker (aeval (fun _ : sigma => (0 : F))).toRingHom)
    (hI : I ≤ RingHom.ker (aeval (fun _ : sigma => (0 : F))).toRingHom)
    (hJI : J ≤ I)

/-- The specified coefficient-algebra quotient map from equation containment. -/
noncomputable def originPolynomialQuotientFactor :
    (MvPolynomial sigma F ⧸ J) →ₐ[F] (MvPolynomial sigma F ⧸ I) :=
  { Ideal.Quotient.factor hJI with
    commutes' a := by rfl }

/-- The actual quotient factor preserves every original polynomial value. -/
theorem originPolynomialQuotientFactor_mk (p : MvPolynomial sigma F) :
    originPolynomialQuotientFactor J I hJI (Ideal.Quotient.mk J p) = Ideal.Quotient.mk I p := rfl

/-- Both original rational-origin evaluations commute with the quotient factor. -/
theorem originPolynomialQuotientFactor_evaluation (x : MvPolynomial sigma F ⧸ J) :
    zeroPointQuotientEvaluation I hI (originPolynomialQuotientFactor J I hJI x) =
      zeroPointQuotientEvaluation J hJ x := by
  obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective x
  rfl

/-- Every denominator outside the source origin prime is a unit
after applying the specified quotient map to the target local ring. -/
theorem originPolynomialQuotientFactor_denominator_unit
    (t : (zeroPointQuotientPrime J hJ).primeCompl) :
    IsUnit (algebraMap (MvPolynomial sigma F ⧸ I) (Localization.AtPrime (zeroPointQuotientPrime I hI))
      (originPolynomialQuotientFactor J I hJI (t : MvPolynomial sigma F ⧸ J))) := by
  have htarget : originPolynomialQuotientFactor J I hJI (t : MvPolynomial sigma F ⧸ J) ∈
      (zeroPointQuotientPrime I hI).primeCompl := by
    change zeroPointQuotientEvaluation I hI (originPolynomialQuotientFactor J I hJI t) ≠ 0
    rw [originPolynomialQuotientFactor_evaluation J I hJ hI hJI]
    exact t.property
  exact IsLocalization.map_units (Localization.AtPrime (zeroPointQuotientPrime I hI)) ⟨_, htarget⟩

/-- The canonical map of the actual local rings at the rational origin. -/
noncomputable def zeroPointLocalQuotientHom :
    Localization.AtPrime (zeroPointQuotientPrime J hJ) →ₐ[F]
      Localization.AtPrime (zeroPointQuotientPrime I hI) :=
  IsLocalization.liftAlgHom
    (f := (IsScalarTower.toAlgHom F (MvPolynomial sigma F ⧸ I)
      (Localization.AtPrime (zeroPointQuotientPrime I hI))).comp (originPolynomialQuotientFactor J I hJI))
    (originPolynomialQuotientFactor_denominator_unit J I hJ hI hJI)

/-- The canonical local map has the original quotient-factor value
on every regular quotient element. -/
theorem zeroPointLocalQuotientHom_base (x : MvPolynomial sigma F ⧸ J) :
    zeroPointLocalQuotientHom J I hJ hI hJI
      (algebraMap (MvPolynomial sigma F ⧸ J) (Localization.AtPrime (zeroPointQuotientPrime J hJ)) x) =
      algebraMap (MvPolynomial sigma F ⧸ I) (Localization.AtPrime (zeroPointQuotientPrime I hI))
        (originPolynomialQuotientFactor J I hJI x) := by
  exact IsLocalization.lift_eq
    (S := Localization.AtPrime (zeroPointQuotientPrime J hJ))
    (g := ((IsScalarTower.toAlgHom F (MvPolynomial sigma F ⧸ I)
      (Localization.AtPrime (zeroPointQuotientPrime I hI))).comp
        (originPolynomialQuotientFactor J I hJI)).toRingHom)
    (originPolynomialQuotientFactor_denominator_unit J I hJ hI hJI) x

/-- In particular, the canonical local map preserves the images
of all original polynomials, not just their residue values. -/
theorem zeroPointLocalQuotientHom_polynomial (p : MvPolynomial sigma F) :
    zeroPointLocalQuotientHom J I hJ hI hJI (zeroPointLocalPolynomialHom J hJ p) =
      zeroPointLocalPolynomialHom I hI p := by
  change zeroPointLocalQuotientHom J I hJ hI hJI
    (algebraMap (MvPolynomial sigma F ⧸ J) (Localization.AtPrime (zeroPointQuotientPrime J hJ))
      (Ideal.Quotient.mk J p)) = _
  rw [zeroPointLocalQuotientHom_base, originPolynomialQuotientFactor_mk]
  rfl

/-- Polynomial equation containment constructs a surjective map
of the actual origin local rings. Both parts of each local fraction
are lifted, and denominator nonvanishing follows from the original point. -/
theorem zeroPointLocalQuotientHom_surjective :
    Function.Surjective (zeroPointLocalQuotientHom J I hJ hI hJI) := by
  have hsurj : Function.Surjective (originPolynomialQuotientFactor J I hJI) :=
    Ideal.Quotient.factor_surjective hJI
  intro a
  obtain ⟨r, s, rfl⟩ := IsLocalization.exists_mk'_eq (zeroPointQuotientPrime I hI).primeCompl a
  obtain ⟨rJ, hr⟩ := hsurj r
  obtain ⟨sJ, hs⟩ := hsurj (s : MvPolynomial sigma F ⧸ I)
  have hsJ : sJ ∈ (zeroPointQuotientPrime J hJ).primeCompl := by
    change zeroPointQuotientEvaluation J hJ sJ ≠ 0
    rw [← originPolynomialQuotientFactor_evaluation J I hJ hI hJI sJ, hs]
    exact s.property
  let t : (zeroPointQuotientPrime J hJ).primeCompl := ⟨sJ, hsJ⟩
  refine ⟨IsLocalization.mk' (Localization.AtPrime (zeroPointQuotientPrime J hJ)) rJ t, ?_⟩
  have he := congrArg (zeroPointLocalQuotientHom J I hJ hI hJI)
    (IsLocalization.mk'_spec' (Localization.AtPrime (zeroPointQuotientPrime J hJ)) rJ t)
  simp only [map_mul, zeroPointLocalQuotientHom_base] at he
  change algebraMap (MvPolynomial sigma F ⧸ I) (Localization.AtPrime (zeroPointQuotientPrime I hI))
      (originPolynomialQuotientFactor J I hJI sJ) *
        zeroPointLocalQuotientHom J I hJ hI hJI
          (IsLocalization.mk' (Localization.AtPrime (zeroPointQuotientPrime J hJ)) rJ t) =
      algebraMap (MvPolynomial sigma F ⧸ I) (Localization.AtPrime (zeroPointQuotientPrime I hI))
        (originPolynomialQuotientFactor J I hJI rJ) at he
  rw [hs, hr] at he
  apply (IsLocalization.map_units (Localization.AtPrime (zeroPointQuotientPrime I hI)) s).mul_left_cancel
  exact he.trans (IsLocalization.mk'_spec' (Localization.AtPrime (zeroPointQuotientPrime I hI)) r s).symm

end DimensionFourDependence
