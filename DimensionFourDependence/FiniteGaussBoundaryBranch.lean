import DimensionFourDependence.ActualBoundaryGaussAlgebraicity

/-! # A finite original Gauss-parameter field contains the actual boundary point

Adjoin the four actual algebraic boundary coordinates to the specified
image of the original Gauss field. The resulting extension is finite
and its point retains its normalization, original four coordinates and
actual ruling equations. The base field is explicitly isomorphic to
the original rational Gauss-parameter field.
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
    (I : ImageRelationWitness H)

local notation "S₀" => FractionRing (MvPolynomial (Fin 4) K)
local notation "Y" => fun i : Fin 3 => algebraMap (MvPolynomial (Fin 4) K) S₀ (H (p i.castSucc))
local notation "L" => coefficientField (K := K) (Y)
local notation "M" => projectiveRatioField (K := K)
  (rationalImageNormal H I.equation) (imageNormalPivot H I)

variable (κ : Type u) [Field κ]
    [Algebra (coefficientField (K := K) (fun i : Fin 3 => algebraMap (MvPolynomial (Fin 4) K)
      (FractionRing (MvPolynomial (Fin 4) K)) (H (p i.castSucc)))) κ]
    [Algebra K κ]
    [IsScalarTower K (coefficientField (K := K) (fun i : Fin 3 => algebraMap (MvPolynomial (Fin 4) K)
      (FractionRing (MvPolynomial (Fin 4) K)) (H (p i.castSucc)))) κ]

local notation "J" => actualBoundaryOriginalGaussField H hrank p hY I κ

/-- The original rational Gauss field is exactly the specified
Gauss-parameter subfield of the actual boundary coefficient extension. -/
noncomputable def actualBoundaryOriginalGaussRationalEquiv
    (e : RatFunc K ≃ₐ[K] projectiveRatioField (K := K)
      (rationalImageNormal H I.equation) (imageNormalPivot H I)) : RatFunc K ≃ₐ[K] (J) :=
  e.trans (((IsScalarTower.toAlgHom K (L) κ).comp
    (actualChartGaussFieldHom H hrank p hY I)).equivFieldRange)

/-- The actual original ruling equations over the actual Gauss image
inside the boundary coefficient field, before adjoining boundary coordinates. -/
noncomputable def actualBoundaryOriginalGaussRulingMatrix
    (e : RatFunc K ≃ₐ[K] projectiveRatioField (K := K)
      (rationalImageNormal H I.equation) (imageNormalPivot H I)) : Matrix (Fin 2) (Fin 4) (J) :=
  (actualGaussRulingMatrix H I e).map (((IsScalarTower.toAlgHom K (L) κ).comp
    (actualChartGaussFieldHom H hrank p hY I)).equivFieldRange)

/-- Algebraic normalized actual ruling coordinates construct a finite
extension of the original Gauss field containing the same actual point,
with its normalization and both actual ruling equations preserved. -/
theorem normalized_algebraic_original_ruling_point_finite_branch
    (e : RatFunc K ≃ₐ[K] projectiveRatioField (K := K)
      (rationalImageNormal H I.equation) (imageNormalPivot H I))
    (b : Fin 4 → κ) (a : Fin 4) (ha : b a = 1)
    (halg : ∀ i, IsAlgebraic (J) (b i))
    (hb : (actualGaussRulingMatrix H I e).map
      ((algebraMap (L) κ).comp (actualChartGaussFieldHom H hrank p hY I).toRingHom) *ᵥ b = 0) :
    ∃ B : IntermediateField (J) κ, Module.Finite (J) B ∧
      ∃ v : Fin 4 → B, v a = 1 ∧ (∀ i, (v i : κ) = b i) ∧
        (actualBoundaryOriginalGaussRulingMatrix H hrank p hY I κ e).map (algebraMap (J) B) *ᵥ v = 0 := by
  let B := IntermediateField.adjoin (J) (Set.range b)
  have hfin : Module.Finite (J) B := IntermediateField.finiteDimensional_adjoin (by
    rintro x ⟨i, rfl⟩
    exact (halg i).isIntegral)
  let v : Fin 4 → B := fun i => ⟨b i, IntermediateField.subset_adjoin (J) _ ⟨i, rfl⟩⟩
  have hv : ∀ i, (v i : κ) = b i := fun _ => rfl
  refine ⟨B, hfin, v, ?_, hv, ?_⟩
  · apply Subtype.ext
    exact ha
  · funext r
    apply (algebraMap B κ).injective
    change algebraMap B κ
      (((actualBoundaryOriginalGaussRulingMatrix H hrank p hY I κ e).map (algebraMap (J) B) *ᵥ v) r) =
      algebraMap B κ 0
    simp only [Matrix.mulVec, dotProduct, map_sum, map_mul, map_zero, Matrix.map_apply]
    change (∑ i, ((algebraMap (L) κ).comp (actualChartGaussFieldHom H hrank p hY I).toRingHom)
      (actualGaussRulingMatrix H I e r i) * b i) = 0
    exact congrFun hb r

include hY

/-- An actual normalized full-fiber boundary point yields a point on
the actual original ruling over a finite extension of its original Gauss
parameter field. All algebraicity and coefficient data are derived. -/
theorem actual_full_fiber_boundary_has_finite_original_gauss_branch
    {d : ℕ} (hd : 0 < d) (hH : IsHomogMap H d) (hN : IsNilpotent (jac H))
    (hind : ¬ ComponentsDependent H) (hGauss : gaussImageDimension H I = 1)
    (h c q : coefficientField (K := K) (fun i : Fin 3 => algebraMap (MvPolynomial (Fin 4) K)
      (FractionRing (MvPolynomial (Fin 4) K)) (H (p i.castSucc))))
    (hh : (h : FractionRing (MvPolynomial (Fin 4) K)) = algebraMap (MvPolynomial (Fin 4) K)
      (FractionRing (MvPolynomial (Fin 4) K)) (H (p 3)))
    (hc : (c : S₀) = firstFiberInvariantInChart p (Y) hY h)
    (hq : (q : S₀) = secondFiberInvariant p (Y) hY h c)
    (z : Option (Fin 4) → κ) (hz : z ≠ 0) (hb : (fun i => z (some i)) ≠ 0)
    (hboundary : projectiveFieldPoint (E := L) z hz ∈ projectiveClosureSet («L» := L) (rationalCoordinate (K := K) (n := 4)))
    (hz0 : z none = 0) (a : Fin 4) (ha : z (some a) = 1) :
    ∃ e : RatFunc K ≃ₐ[K] projectiveRatioField (K := K)
      (rationalImageNormal H I.equation) (imageNormalPivot H I),
      Module.finrank (M) (LinearMap.ker (actualGaussRulingMatrix H I e).toLin') = 2 ∧
      ∃ B : IntermediateField (J) κ, Module.Finite (J) B ∧
        ∃ v : Fin 4 → B, v a = 1 ∧ (∀ i, (v i : κ) = z (some i)) ∧
          (actualBoundaryOriginalGaussRulingMatrix H hrank p hY I κ e).map (algebraMap (J) B) *ᵥ v = 0 := by
  obtain ⟨e, hA, _⟩ := actual_gauss_fiber_ruling_polynomial_density H hd hH hrank hind I hGauss
  have halg := actual_full_fiber_boundary_coordinates_algebraic_over_original_gauss H hrank p hY
    hd hH hN hind I hGauss h c q hh hc hq κ z hz hb hboundary hz0 a ha
  have hruling := actual_full_fiber_boundary_mem_original_gauss_ruling H hrank p hY I e h hh
    hd hH hGauss c q hc hq κ z hz hboundary hz0
  exact ⟨e, hA, normalized_algebraic_original_ruling_point_finite_branch H hrank p hY I κ e
    (fun i => z (some i)) a ha halg hruling⟩

end DimensionFourDependence
