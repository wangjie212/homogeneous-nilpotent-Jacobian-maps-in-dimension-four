import DimensionFourDependence.HomogeneousSectionMultiplication
import DimensionFourDependence.ProjectiveDehomogenizedIdeal
import DimensionFourDependence.HomogeneousProjectiveSubstitution

/-! # A single rational projective support bounds the global Hilbert function

For an eventually constant actual Hilbert function, the homogeneous
quotient pieces inject into the actual affine-origin local ring in all
sufficiently large degrees when the projective support is that origin.
All denominators are cleared in the original homogeneous ideal. No
assumed local-to-global degree or dimension comparison is used.
-/

namespace DimensionFourDependence

open MvPolynomial Module

attribute [local instance] MvPolynomial.gradedAlgebra

variable {F sigma : Type*} [Field F]

/-- The homogeneous vector of the rational origin of the standard chart. -/
theorem projective_chart_origin_coordinates_ne_zero :
    (fun j : Option sigma => j.elim (1 : F) (fun _ => 0)) ≠ 0 := by
  intro hzero
  have he := congrFun hzero none
  exact one_ne_zero he

/-- The actual projective-spectrum point at the rational origin of
the chart whose homogeneous coordinate is one. -/
noncomputable def projectiveChartOriginPoint :
    ProjectiveSpectrum (homogeneousSubmodule (Option sigma) F) :=
  projectiveFieldPoint (E := F) (fun j : Option sigma => j.elim 1 (fun _ => (0 : F)))
    projective_chart_origin_coordinates_ne_zero

/-- An original homogeneous equation belongs to that point exactly
when its actual affine-origin value vanishes. -/
theorem projectiveChartOriginPoint_homogeneous_mem
    (S : MvPolynomial (Option sigma) F) {d : ℕ} (hS : S.IsHomogeneous d) :
    S ∈ (projectiveChartOriginPoint (F := F) (sigma := sigma)).asHomogeneousIdeal ↔
      aeval (fun j : Option sigma => j.elim 1 (fun _ => (0 : F))) S = 0 :=
  projectiveFieldPoint_homogeneous_mem _ _ S hS

/-- The actual map from each homogeneous quotient piece to its
dehomogenized quotient's actual rational-origin localization. -/
noncomputable def homogeneousOriginLocalChartMap
    (I : Ideal (MvPolynomial (Option sigma) F))
    (hJ : projectiveDehomogenizedIdeal I ≤ RingHom.ker (aeval (fun _ : sigma => (0 : F))).toRingHom)
    (n : ℕ) :
    ((homogeneousSubmodule (Option sigma) F n) ⧸ homogeneousRelationSpace I n) →ₗ[F]
      Localization.AtPrime (zeroPointQuotientPrime (projectiveDehomogenizedIdeal I) hJ) := by
  let phi : MvPolynomial sigma F →ₐ[F]
      Localization.AtPrime (zeroPointQuotientPrime (projectiveDehomogenizedIdeal I) hJ) :=
    zeroPointLocalPolynomialHom (projectiveDehomogenizedIdeal I) hJ
  let f : homogeneousSubmodule (Option sigma) F n →
      Localization.AtPrime (zeroPointQuotientPrime (projectiveDehomogenizedIdeal I) hJ) :=
    fun P => phi (projectiveDehomogenize (P : MvPolynomial (Option sigma) F))
  have hf : ∀ P Q, (homogeneousRelationSpace I n).quotientRel P Q → f P = f Q := by
    intro P Q hrel
    have hmem := (Submodule.quotientRel_def (homogeneousRelationSpace I n)).mp hrel
    have he := zeroPointLocalPolynomialHom_relation (projectiveDehomogenizedIdeal I) hJ _
      (Ideal.mem_map_of_mem (projectiveDehomogenize (R := F) (σ := sigma)).toRingHom hmem)
    change phi (projectiveDehomogenize (P : MvPolynomial (Option sigma) F)) =
      phi (projectiveDehomogenize (Q : MvPolynomial (Option sigma) F))
    apply sub_eq_zero.mp
    change phi (projectiveDehomogenize ((P : MvPolynomial (Option sigma) F) - Q)) = 0 at he
    simpa only [map_sub] using he
  refine { toFun := Quotient.lift f hf, map_add' := ?_, map_smul' := ?_ }
  · intro a b
    refine Quotient.inductionOn₂ a b ?_
    intro P Q
    change phi (projectiveDehomogenize ((P : MvPolynomial (Option sigma) F) + Q)) =
      phi (projectiveDehomogenize P) + phi (projectiveDehomogenize Q)
    rw [map_add, map_add]
  · intro a b
    refine Quotient.inductionOn b ?_
    intro P
    change phi (projectiveDehomogenize (a • (P : MvPolynomial (Option sigma) F))) =
      a • phi (projectiveDehomogenize P)
    rw [map_smul, map_smul]

/-- A homogeneous form whose actual local-chart value is zero is an
original relation in all sufficiently large degrees, when all projective
support is the rational origin and the Hilbert function is constant. -/
theorem homogeneous_origin_local_chart_eventual_relation
    [Finite sigma] (I : Ideal (MvPolynomial (Option sigma) F))
    (hI : I.IsHomogeneous (homogeneousSubmodule (Option sigma) F))
    (hJ : projectiveDehomogenizedIdeal I ≤ RingHom.ker (aeval (fun _ : sigma => (0 : F))).toRingHom)
    (e N : ℕ) (hN : ∀ n ≥ N, projectiveHilbertFunction I n = e)
    (hsupport : ∀ z : ProjectiveSpectrum (homogeneousSubmodule (Option sigma) F),
      I ≤ z.asHomogeneousIdeal.toIdeal → z = projectiveChartOriginPoint) :
    ∃ M : ℕ, ∀ n ≥ M, ∀ P : MvPolynomial (Option sigma) F,
      P.IsHomogeneous n →
      zeroPointLocalPolynomialHom (projectiveDehomogenizedIdeal I) hJ (projectiveDehomogenize P) = 0 →
      P ∈ I := by
  have htavoid : ∀ z : ProjectiveSpectrum (homogeneousSubmodule (Option sigma) F),
      I ≤ z.asHomogeneousIdeal.toIdeal → X none ∉ z.asHomogeneousIdeal := by
    intro z hz
    rw [hsupport z hz, projectiveChartOriginPoint_homogeneous_mem _ (isHomogeneous_X (R := F) none)]
    simp
  obtain ⟨M, hM⟩ := homogeneous_section_eventual_cancel_of_support_avoids I hI e N hN
    (X none) (isHomogeneous_X (R := F) none) htavoid
  refine ⟨M, ?_⟩
  intro n hn P hP hzero
  obtain ⟨d, S, hS, hs0, hSP⟩ :=
    origin_local_dehomogenized_vanishing_homogeneous_denominator I hI hJ P hP hzero
  have hSavoid : ∀ z : ProjectiveSpectrum (homogeneousSubmodule (Option sigma) F),
      I ≤ z.asHomogeneousIdeal.toIdeal → S ∉ z.asHomogeneousIdeal := by
    intro z hz
    rw [hsupport z hz, projectiveChartOriginPoint_homogeneous_mem S hS]
    exact hs0
  obtain ⟨M', hM'⟩ := homogeneous_section_eventual_cancel_of_support_avoids I hI e N hN S hS hSavoid
  have hpower : X none ^ M' * P ∈ I := by
    apply hM' (n + M') (by omega) (X none ^ M' * P)
    · simpa only [Nat.add_comm] using (isHomogeneous_X_pow (R := F) (none : Option sigma) M').mul hP
    · simpa only [mul_left_comm] using I.mul_mem_left (X none ^ M') hSP
  have hcancel : ∀ k : ℕ, X none ^ k * P ∈ I → P ∈ I := by
    intro k
    induction k with
    | zero =>
      intro hk
      simpa only [pow_zero, one_mul] using hk
    | succ k ih =>
      intro hk
      apply ih
      apply hM (n + k) (by omega) (X none ^ k * P)
      · simpa only [Nat.add_comm] using (isHomogeneous_X_pow (R := F) (none : Option sigma) k).mul hP
      · simpa only [pow_succ, mul_assoc, mul_left_comm] using hk
  exact hcancel M' hpower

/-- The actual global graded quotient injects into its actual local
chart algebra in every sufficiently large degree. -/
theorem homogeneousOriginLocalChartMap_eventually_injective
    [Finite sigma] (I : Ideal (MvPolynomial (Option sigma) F))
    (hI : I.IsHomogeneous (homogeneousSubmodule (Option sigma) F))
    (hJ : projectiveDehomogenizedIdeal I ≤ RingHom.ker (aeval (fun _ : sigma => (0 : F))).toRingHom)
    (e N : ℕ) (hN : ∀ n ≥ N, projectiveHilbertFunction I n = e)
    (hsupport : ∀ z : ProjectiveSpectrum (homogeneousSubmodule (Option sigma) F),
      I ≤ z.asHomogeneousIdeal.toIdeal → z = projectiveChartOriginPoint) :
    ∃ M : ℕ, ∀ n ≥ M, Function.Injective (homogeneousOriginLocalChartMap I hJ n) := by
  obtain ⟨M, hM⟩ := homogeneous_origin_local_chart_eventual_relation I hI hJ e N hN hsupport
  refine ⟨M, ?_⟩
  intro n hn a b hab
  obtain ⟨P, rfl⟩ := (homogeneousRelationSpace I n).mkQ_surjective a
  obtain ⟨Q, rfl⟩ := (homogeneousRelationSpace I n).mkQ_surjective b
  apply (Submodule.Quotient.eq (homogeneousRelationSpace I n)).mpr
  apply hM n hn (P - Q) (P - Q).property
  rw [map_sub, map_sub]
  exact sub_eq_zero.mpr hab

/-- The eventual actual Hilbert value is bounded by the coefficient
dimension of the actual rational-origin localization, with no supplied
local-to-global comparison. -/
theorem projective_hilbert_value_le_actual_origin_local_dimension
    [Finite sigma] (I : Ideal (MvPolynomial (Option sigma) F))
    (hI : I.IsHomogeneous (homogeneousSubmodule (Option sigma) F))
    (hJ : projectiveDehomogenizedIdeal I ≤ RingHom.ker (aeval (fun _ : sigma => (0 : F))).toRingHom)
    [Module.Finite F (Localization.AtPrime (zeroPointQuotientPrime (projectiveDehomogenizedIdeal I) hJ))]
    (e N : ℕ) (hN : ∀ n ≥ N, projectiveHilbertFunction I n = e)
    (hsupport : ∀ z : ProjectiveSpectrum (homogeneousSubmodule (Option sigma) F),
      I ≤ z.asHomogeneousIdeal.toIdeal → z = projectiveChartOriginPoint) :
    e ≤ finrank F (Localization.AtPrime (zeroPointQuotientPrime (projectiveDehomogenizedIdeal I) hJ)) := by
  obtain ⟨M, hM⟩ := homogeneousOriginLocalChartMap_eventually_injective I hI hJ e N hN hsupport
  have hdim := LinearMap.finrank_le_finrank_of_injective (hM (max N M) (le_max_right N M))
  change projectiveHilbertFunction I (max N M) ≤ _ at hdim
  rwa [hN (max N M) (le_max_left N M)] at hdim

end DimensionFourDependence
