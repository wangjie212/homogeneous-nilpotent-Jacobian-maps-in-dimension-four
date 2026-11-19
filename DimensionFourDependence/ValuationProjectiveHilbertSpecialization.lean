import DimensionFourDependence.ValuationResidueSpanDimension
import DimensionFourDependence.ProjectivePointHilbertEvaluation
import DimensionFourDependence.GeometricHilbertBound

/-! # Valuative specialization cannot increase projective curve degree -/

namespace DimensionFourDependence

open MvPolynomial Module

attribute [local instance] MvPolynomial.gradedAlgebra

set_option maxHeartbeats 2500000
set_option synthInstance.maxHeartbeats 100000

variable {K F A κ σ : Type*} [Field K] [Field F] [CommRing A] [Field κ]
  [Algebra K F] [Finite σ]

/-- Every degree of the actual projective residue coordinate ideal
has Hilbert function at most the corresponding generic degree. -/
theorem projectiveHilbertFunction_residue_le_generic
    (V : ValuationSubring K) [Algebra V A] [Algebra A F] [Algebra V F]
    [IsScalarTower V A F] [IsScalarTower V K F]
    [Algebra (IsLocalRing.ResidueField V) κ]
    (hinj : Function.Injective (algebraMap A F)) (π : A →+* κ)
    (hcompat : ∀ a : V, π (algebraMap V A a) =
      algebraMap (IsLocalRing.ResidueField V) κ (IsLocalRing.residue V a))
    (z : σ → A) (d : ℕ) :
    projectiveHilbertFunction (projectiveFieldPointIdeal (E := IsLocalRing.ResidueField V)
        (fun i => π (z i))).toIdeal d ≤
      projectiveHilbertFunction (projectiveFieldPointIdeal (E := K)
        (fun i => algebraMap A F (z i))).toIdeal d := by
  classical
  let M := {m : σ →₀ ℕ // m.degree = d}
  let : Fintype M := (Finsupp.finite_of_degree_eq d).fintype
  let e := Fintype.equivFin M
  let zmon : Fin (Fintype.card M) → A := fun j => (e.symm j).val.prod (fun i n => z i ^ n)
  have hπ (m : M) : π (m.val.prod (fun i n => z i ^ n)) =
      m.val.prod (fun i n => π (z i) ^ n) := by
    simp only [Finsupp.prod, map_prod, map_pow]
  have hgeneric (m : M) : algebraMap A F (m.val.prod (fun i n => z i ^ n)) =
      m.val.prod (fun i n => algebraMap A F (z i) ^ n) := by
    simp only [Finsupp.prod, map_prod, map_pow]
  have hresRange : Set.range (fun j => π (zmon j)) =
      Set.range (fun m : M => m.val.prod (fun i n => π (z i) ^ n)) := by
    ext y
    constructor
    · rintro ⟨j, rfl⟩
      exact ⟨e.symm j, (hπ (e.symm j)).symm⟩
    · rintro ⟨m, rfl⟩
      refine ⟨e m, ?_⟩
      simpa only [zmon, e.symm_apply_apply] using hπ m
  have hgenericRange : Set.range (fun j => algebraMap A F (zmon j)) =
      Set.range (fun m : M => m.val.prod (fun i n => algebraMap A F (z i) ^ n)) := by
    ext y
    constructor
    · rintro ⟨j, rfl⟩
      exact ⟨e.symm j, (hgeneric (e.symm j)).symm⟩
    · rintro ⟨m, rfl⟩
      refine ⟨e m, ?_⟩
      simpa only [zmon, e.symm_apply_apply] using hgeneric m
  have he := valuation_residue_span_finrank_le_generic V hinj π hcompat zmon
  rw [hresRange, hgenericRange] at he
  simpa only [projectiveHilbertFunction_point_eq_monomial_span_finrank] using he

/-- The same full Hilbert-function bound holds after any specified
nonzero common normalization of the original generic coordinates. -/
theorem projectiveHilbertFunction_normalized_residue_le_generic
    (V : ValuationSubring K) [Algebra V A] [Algebra A F] [Algebra V F]
    [IsScalarTower V A F] [IsScalarTower V K F]
    [Algebra (IsLocalRing.ResidueField V) κ]
    (hinj : Function.Injective (algebraMap A F)) (π : A →+* κ)
    (hcompat : ∀ a : V, π (algebraMap V A a) =
      algebraMap (IsLocalRing.ResidueField V) κ (IsLocalRing.residue V a))
    (x : σ → F) (s : F) (hs : s ≠ 0) (z : σ → A)
    (hz : ∀ i, algebraMap A F (z i) = s * x i) (d : ℕ) :
    projectiveHilbertFunction (projectiveFieldPointIdeal (E := IsLocalRing.ResidueField V)
        (fun i => π (z i))).toIdeal d ≤
      projectiveHilbertFunction (projectiveFieldPointIdeal (E := K) x).toIdeal d := by
  have he := projectiveHilbertFunction_residue_le_generic V hinj π hcompat z d
  have hcoords : (fun i => algebraMap A F (z i)) = (fun i => s * x i) := funext hz
  rwa [hcoords, projectiveFieldPointIdeal_scale x s hs] at he

omit [Field F] [CommRing A] [Algebra K F] [Finite σ] in
/-- A Hilbert-function comparison over possibly different fields
compares the actual positive integral curve degrees. -/
theorem curveHilbertDegree_le_of_hilbertFunction_le {τ : Type*}
    (I : Ideal (MvPolynomial σ K)) (J : Ideal (MvPolynomial τ κ))
    (hbound : ∀ d, projectiveHilbertFunction J d ≤ projectiveHilbertFunction I d)
    {e e' : ℕ} (he : HasCurveHilbertDegree I e) (he' : HasCurveHilbertDegree J e') : e' ≤ e := by
  obtain ⟨_hepos, b, N, hN⟩ := he
  obtain ⟨_he'pos, b', M, hM⟩ := he'
  have hslope := integer_linear_slope_le (e' : ℤ) b' (e : ℤ) b (max N M) (by
    intro n hn
    have hdim : (projectiveHilbertFunction J n : ℤ) ≤ projectiveHilbertFunction I n := by
      exact_mod_cast hbound n
    rw [hN n (by omega), hM n (by omega)] at hdim
    exact hdim)
  exact_mod_cast hslope

/-- A nonconstant projective residue curve has no larger degree
than the generic curve under a compatible valuation specialization,
including any nonzero common rescaling of all generic coordinates. -/
theorem projective_curve_degree_normalized_residue_le_generic
    (V : ValuationSubring K) [Algebra V A] [Algebra A F] [Algebra V F]
    [IsScalarTower V A F] [IsScalarTower V K F]
    [Algebra (IsLocalRing.ResidueField V) κ]
    (hinj : Function.Injective (algebraMap A F)) (π : A →+* κ)
    (hcompat : ∀ a : V, π (algebraMap V A a) =
      algebraMap (IsLocalRing.ResidueField V) κ (IsLocalRing.residue V a))
    (x : σ → F) (s : F) (hs : s ≠ 0) (z : σ → A)
    (hz : ∀ i, algebraMap A F (z i) = s * x i)
    {e e' : ℕ} (he : HasCurveHilbertDegree (projectiveFieldPointIdeal (E := K) x).toIdeal e)
    (he' : HasCurveHilbertDegree (projectiveFieldPointIdeal (E := IsLocalRing.ResidueField V)
      (fun i => π (z i))).toIdeal e') : e' ≤ e := by
  exact curveHilbertDegree_le_of_hilbertFunction_le _ _
    (projectiveHilbertFunction_normalized_residue_le_generic V hinj π hcompat x s hs z hz) he he'

end DimensionFourDependence
