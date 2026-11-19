import DimensionFourDependence.ActualBoundaryRulingParameter

/-! # Actual boundary directions on the original ruling are not generic

Ruling membership now derives the parameter comparison required by
Lemma 4.3. Homogeneous parameter representatives, their nonvanishing,
the actual target value and the contradiction are constructed inside
the proof. Constructing the closed boundary-incidence image and its
finite parameter branches is a subsequent step.
-/

namespace DimensionFourDependence

open MvPolynomial Matrix

attribute [local instance] coefficientFieldScalarTower

universe u

set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 100000
set_option quotPrecheck false

variable {K : Type u} [Field K] [CharZero K]
    (H : Fin 4 → MvPolynomial (Fin 4) K) (hrank : polyRank (jac H) = 3)
    (p : Equiv.Perm (Fin 4))
    (hY : AlgebraicIndependent K (fun i : Fin 3 => algebraMap (MvPolynomial (Fin 4) K)
      (FractionRing (MvPolynomial (Fin 4) K)) (H (p i.castSucc))))

local notation "S₀" => FractionRing (MvPolynomial (Fin 4) K)
local notation "Y" => fun i : Fin 3 => algebraMap (MvPolynomial (Fin 4) K) S₀ (H (p i.castSucc))
local notation "L" => coefficientField (K := K) (Y)
local notation "x" => rationalCoordinate (K := K) (n := 4)

include hY

/-- Every actual full-fiber boundary direction on the actual original
Gauss ruling is nongeneric on the original image. The original parameter
comparison and its homogeneous quotient are conclusions of the proof. -/
theorem actual_full_fiber_boundary_on_original_ruling_not_generic
    {d : ℕ} (hd : 0 < d) (hH : IsHomogMap H d) (hH0 : H ≠ 0)
    (hN : IsNilpotent (jac H)) (hind : ¬ ComponentsDependent H) (I : ImageRelationWitness H)
    (hGauss : gaussImageDimension H I = 1)
    (e : RatFunc K ≃ₐ[K] projectiveRatioField (K := K)
      (rationalImageNormal H I.equation) (imageNormalPivot H I))
    (hA : Module.finrank
      (projectiveRatioField (K := K) (rationalImageNormal H I.equation) (imageNormalPivot H I))
      (LinearMap.ker (actualGaussRulingMatrix H I e).toLin') = 2)
    (g : MvPolynomial (Fin 4) K) (hg : g ≠ 0) (P : Fin 4 → MvPolynomial (Fin 4) K)
    {D : ℕ} (hD : 0 < D) (hP : IsHomogMap P D) (hprim : IsPrimitiveVec P) (hHP : H = fun i => g * P i)
    (κ : Type u) [Field κ] [Algebra (L) κ] [Algebra K κ] [IsScalarTower K (L) κ]
    (z : Option (Fin 4) → κ) (hz : z ≠ 0) (hb : (fun i => z (some i)) ≠ 0)
    (hboundary : projectiveFieldPoint (E := L) z hz ∈ projectiveClosureSet («L» := L) (x))
    (hruling : (actualGaussRulingMatrix H I e).map
      ((algebraMap (L) κ).comp (actualChartGaussFieldHom H hrank p hY I).toRingHom) *ᵥ
        (fun i => z (some i)) = 0) :
    projectiveFieldPoint (E := K) (fun i => z (some i)) hb ≠ projectiveImageGenericPoint H hd hH hH0 := by
  obtain ⟨r, s, m, hscone, hr, hs, ht⟩ := original_cone_gauss_parameter_homogeneous_fraction H I e
  intro hgeneric
  have hcompare := actual_boundary_original_parameter_comparison_of_ruling H hrank p hY
    hd hH hH0 I hGauss e hA r s hs hscone ht κ (fun i => z (some i)) hb hgeneric hruling
  exact actual_full_fiber_boundary_not_generic_of_parameter_comparison H hrank p hY
    hd hH hH0 hN hind I e g hg P hD hP hprim hHP κ z hz hb hboundary r s hr hs hscone ht hcompare hgeneric

/-- The original nonplanar rank-three map of Gauss dimension one
constructs a two-dimensional original ruling on which no actual
full-fiber boundary direction can be generic. No parameter presentation,
normal-jet independence or parameter comparison is supplied. -/
theorem actual_original_ruling_with_boundary_genericity_exclusion
    {d : ℕ} (hd : 0 < d) (hH : IsHomogMap H d) (hH0 : H ≠ 0)
    (hN : IsNilpotent (jac H)) (hind : ¬ ComponentsDependent H) (I : ImageRelationWitness H)
    (hGauss : gaussImageDimension H I = 1)
    (g : MvPolynomial (Fin 4) K) (hg : g ≠ 0) (P : Fin 4 → MvPolynomial (Fin 4) K)
    {D : ℕ} (hD : 0 < D) (hP : IsHomogMap P D) (hprim : IsPrimitiveVec P) (hHP : H = fun i => g * P i) :
    ∃ e : RatFunc K ≃ₐ[K] projectiveRatioField (K := K)
      (rationalImageNormal H I.equation) (imageNormalPivot H I),
      Module.finrank
        (projectiveRatioField (K := K) (rationalImageNormal H I.equation) (imageNormalPivot H I))
        (LinearMap.ker (actualGaussRulingMatrix H I e).toLin') = 2 ∧
      ∀ (κ : Type u) [Field κ] [Algebra (L) κ] [Algebra K κ] [IsScalarTower K (L) κ]
        (z : Option (Fin 4) → κ) (hz : z ≠ 0) (hb : (fun i => z (some i)) ≠ 0),
        projectiveFieldPoint (E := L) z hz ∈ projectiveClosureSet («L» := L) (x) →
        (actualGaussRulingMatrix H I e).map
          ((algebraMap (L) κ).comp (actualChartGaussFieldHom H hrank p hY I).toRingHom) *ᵥ
            (fun i => z (some i)) = 0 →
        projectiveFieldPoint (E := K) (fun i => z (some i)) hb ≠ projectiveImageGenericPoint H hd hH hH0 := by
  obtain ⟨e, hA, _⟩ := actual_gauss_fiber_ruling_polynomial_density H hd hH hrank hind I hGauss
  exact ⟨e, hA, fun κ _ _ _ _ z hz hb hboundary hruling =>
    actual_full_fiber_boundary_on_original_ruling_not_generic H hrank p hY hd hH hH0 hN hind I hGauss
      e hA g hg P hD hP hprim hHP κ z hz hb hboundary hruling⟩

end DimensionFourDependence
