import DimensionFourDependence.PrimitiveDehomogenization
import DimensionFourDependence.ProjectiveSourceSections
import DimensionFourDependence.SourceDivisorLocalization

/-! # Original homogeneous common-factor degree from projective chart orders

A prime chart equation has its actual homogeneous divisor equation in
the original four source coordinates. Chart orders on all original map
sections force that same homogeneous divisor power into the original
common factor g, and hence give a <= degree(g).
-/

namespace DimensionFourDependence

open MvPolynomial

variable {K : Type*} [Field K]

local notation "R₄" => MvPolynomial (Fin 4) K

/-- The original homogeneous equation of a chart divisor, in the
original source coordinate order rather than the reindexed chart order. -/
noncomputable def projectiveSourceHomogeneousDivisor
    (s : Fin 4 ≃ Option (Fin 3)) (δ : MvPolynomial (Fin 3) K) : R₄ :=
  (renameEquiv K s).symm (projectiveHomogenize δ δ.totalDegree)

/-- Its chart equation is exactly the given divisor equation. -/
theorem projectiveSourceHomogeneousDivisor_dehomogenize
    (s : Fin 4 ≃ Option (Fin 3)) (δ : MvPolynomial (Fin 3) K) :
    projectiveSourceDehomogenize s (projectiveSourceHomogeneousDivisor s δ) = δ := by
  change projectiveDehomogenize ((renameEquiv K s)
    ((renameEquiv K s).symm (projectiveHomogenize δ δ.totalDegree))) = δ
  rw [AlgEquiv.apply_symm_apply, projectiveDehomogenize_homogenize]

/-- The homogeneous closure equation of an irreducible chart divisor
is irreducible in the original four source variables. -/
theorem projectiveSourceHomogeneousDivisor_irreducible
    (s : Fin 4 ≃ Option (Fin 3)) (δ : MvPolynomial (Fin 3) K) (hδ : Irreducible δ) :
    Irreducible (projectiveSourceHomogeneousDivisor s δ) :=
  (MulEquiv.irreducible_iff (f := (renameEquiv K s).symm.toMulEquiv)).mpr
    (projectiveHomogenize_irreducible δ hδ)

/-- Its actual original homogeneous degree is the chart equation's degree. -/
theorem projectiveSourceHomogeneousDivisor_totalDegree
    (s : Fin 4 ≃ Option (Fin 3)) (δ : MvPolynomial (Fin 3) K) (hδ : δ ≠ 0) :
    (projectiveSourceHomogeneousDivisor s δ).totalDegree = δ.totalDegree := by
  change (renameEquiv K s.symm (projectiveHomogenize δ δ.totalDegree)).totalDegree = δ.totalDegree
  rw [totalDegree_renameEquiv, projectiveHomogenize_totalDegree hδ _ le_rfl]

/-- The closure equation is homogeneous in the original source variables. -/
theorem projectiveSourceHomogeneousDivisor_isHomogeneous
    (s : Fin 4 ≃ Option (Fin 3)) (δ : MvPolynomial (Fin 3) K) :
    (projectiveSourceHomogeneousDivisor s δ).IsHomogeneous δ.totalDegree :=
  (projectiveHomogenize_isHomogeneous δ δ.totalDegree le_rfl).rename_isHomogeneous

/-- Prime-power divisibility in the chosen projective chart forces the
same original homogeneous divisor power into the original common factor. -/
theorem projective_chart_common_factor_degree
    (s : Fin 4 ≃ Option (Fin 3)) (H P : Fin 4 → R₄) (g : R₄) {c d : ℕ}
    (hg : g ≠ 0) (hgh : g.IsHomogeneous c) (hP : IsHomogMap P d)
    (hprim : IsPrimitiveVec P) (hHP : H = fun i => g * P i)
    (δ : MvPolynomial (Fin 3) K) (hδ : Irreducible δ) (a : ℕ)
    (hdiv : ∀ i, δ ^ a ∣ projectiveSourceDehomogenize s (H i)) :
    projectiveSourceHomogeneousDivisor s δ ^ a ∣ g ∧
      a * δ.totalDegree ≤ g.totalDegree ∧ a ≤ g.totalDegree := by
  let e := renameEquiv K s
  have hP' : IsHomogMap (fun i => e (P i)) d := fun i => (hP i).rename_isHomogeneous
  have hprim' := isPrimitiveVec_map_algEquiv e P hprim
  have hHP' : (fun i => e (H i)) = (fun i => e g * e (P i)) := by
    funext i
    rw [congrFun hHP i, map_mul]
  have hdiv' : ∀ i, δ ^ a ∣ projectiveDehomogenize (e (H i)) := hdiv
  obtain ⟨hpow, hdeg, hsmall⟩ := dehomogenized_source_common_factor_degree
    (fun i => e (H i)) (fun i => e (P i)) (e g)
    (by simpa using e.injective.ne hg) hgh.rename_isHomogeneous hP' hprim' hHP' δ hδ a hdiv'
  have hback := map_dvd e.symm.toRingHom hpow
  change e.symm (projectiveHomogenize δ δ.totalDegree ^ a) ∣ e.symm (e g) at hback
  have hsource : projectiveSourceHomogeneousDivisor s δ ^ a ∣ g := by
    change e.symm (projectiveHomogenize δ δ.totalDegree) ^ a ∣ g
    simpa only [map_pow, AlgEquiv.symm_apply_apply] using hback
  have hedeg : (e g).totalDegree = g.totalDegree := totalDegree_renameEquiv s g
  exact ⟨hsource, hedeg ▸ hdeg, hedeg ▸ hsmall⟩

/-- The source-divisor local order of every actual projective section
coefficient forces original homogeneous common-factor divisibility and degree. -/
theorem projective_source_divisor_orders_common_factor_degree
    (s : Fin 4 ≃ Option (Fin 3)) (H P : Fin 4 → R₄) (g : R₄) {c d : ℕ}
    (hg : g ≠ 0) (hgh : g.IsHomogeneous c) (hP : IsHomogMap P d)
    (hprim : IsPrimitiveVec P) (hHP : H = fun i => g * P i)
    (δ : MvPolynomial (Fin 3) K) (hδ : Irreducible δ)
    (Q : Ideal (projectiveCoordinateChartAlgebra (C := K)
      (rationalCoordinate (K := K) (n := 4)) (s.symm none))) [Q.IsPrime]
    (hQ : Q = Ideal.span {projectiveSourceFullChartCoordinateEquiv s δ}) (a : ℕ)
    (horder : ∀ i, algebraMap _ (Localization.AtPrime Q) (projectiveSourceSectionHom s (H i)) ∈
      (IsLocalRing.maximalIdeal (Localization.AtPrime Q)) ^ a) :
    projectiveSourceHomogeneousDivisor s δ ^ a ∣ g ∧
      a * δ.totalDegree ≤ g.totalDegree ∧ a ≤ g.totalDegree := by
  apply projective_chart_common_factor_degree s H P g hg hgh hP hprim hHP δ hδ a
  let e := projectiveSourceFullChartCoordinateEquiv (K := K) s
  have hf : Prime (e δ) := (MulEquiv.prime_iff e).mpr (irreducible_iff_prime.mp hδ)
  intro i
  have hdiv := (principal_prime_localization_power_mem_iff Q (e δ) hf hQ
    (projectiveSourceSectionHom s (H i)) a).mp (horder i)
  have hback := map_dvd e.symm.toRingHom hdiv
  change e.symm (e δ ^ a) ∣ e.symm (e (projectiveSourceDehomogenize s (H i))) at hback
  simpa only [map_pow, AlgEquiv.symm_apply_apply] using hback

end DimensionFourDependence
