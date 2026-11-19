import DimensionFourDependence.RadialTraceObstruction
import DimensionFourDependence.HomogeneousPowerRemoval

/-! # The primitive map cannot fix the generic nonlinear image

This completes the algebraic fixed-point exclusion of Section 3.1.
The maximal common power is constructed, primitive radial congruences
pass to its quotient, and the checked trace contradiction applies even
when the original common factor vanishes on the image hypersurface.
-/

namespace DimensionFourDependence

open MvPolynomial

variable {K : Type*} [Field K]

/-- A nonlinear homogeneous equation cannot divide a source coordinate. -/
theorem nonlinear_homogeneous_not_dvd_coordinate
    (R : MvPolynomial (Fin 4) K) {n : ℕ} (hn : 2 ≤ n)
    (hR0 : R ≠ 0) (hRh : R.IsHomogeneous n) (j : Fin 4) : ¬ R ∣ X j := by
  intro hdiv
  have he := homogeneous_power_dvd_degree_bound R (X j) hR0 hRh (X_ne_zero j) 1
    (by simpa only [pow_one] using hdiv)
  simp only [mul_one, totalDegree_X] at he
  omega

/-- Cross-coordinate radial congruences give an actual cleared polynomial presentation. -/
theorem radial_cross_relations_presentation
    (R : MvPolynomial (Fin 4) K) (V : Fin 4 → MvPolynomial (Fin 4) K) (j : Fin 4)
    (hcross : ∀ i, R ∣ X j * V i - X i * V j) :
    ∃ W : Fin 4 → MvPolynomial (Fin 4) K,
      (fun i => X j * V i) = fun i => V j * X i + R * W i := by
  classical
  choose W hW using hcross
  refine ⟨W, funext fun i => ?_⟩
  linear_combination hW i

/-- Primitivity lets radial congruences survive division by the maximal
common image-equation power of the original map. -/
theorem primitive_cross_relations_remove_common_power
    (R : MvPolynomial (Fin 4) K) (hR : Irreducible R)
    (H P V : Fin 4 → MvPolynomial (Fin 4) K) (g : MvPolynomial (Fin 4) K)
    (hP : IsPrimitiveVec P) (hHP : H = fun i => g * P i) (m : ℕ)
    (hHV : H = fun i => R ^ m * V i)
    (hcross : ∀ i j, R ∣ X i * P j - X j * P i) :
    ∀ i j, R ∣ X i * V j - X j * V i := by
  classical
  obtain ⟨a, ha⟩ : ∃ a, ¬ R ∣ P a := by
    by_contra hn
    push Not at hn
    exact hR.not_isUnit (hP R hn)
  have hp : R ^ m ∣ g * P a := ⟨V a, by rw [← congrFun hHP a, congrFun hHV a]⟩
  obtain ⟨b, hb⟩ := hR.prime.pow_dvd_of_dvd_mul_right m ha hp
  have hV (i : Fin 4) : V i = b * P i := by
    apply mul_left_cancel₀ (pow_ne_zero m hR.ne_zero)
    have he := (congrFun hHV i).symm.trans (congrFun hHP i)
    rw [hb] at he
    linear_combination he
  intro i j
  rw [hV i, hV j]
  have he : X i * (b * P j) - X j * (b * P i) = b * (X i * P j - X j * P i) := by ring
  rw [he]
  exact dvd_mul_of_dvd_right (hcross i j) b

/-- The algebraic fixed-point assertion is impossible on a nonlinear
homogeneous image hypersurface of a divergence-zero homogeneous map. -/
theorem primitive_map_not_radial_on_nonlinear_image [CharZero K]
    (H : Fin 4 → MvPolynomial (Fin 4) K) {d : ℕ} (hH : IsHomogMap H d) (hH0 : H ≠ 0)
    (hdiv : divergence H = 0) (R : MvPolynomial (Fin 4) K) {n : ℕ}
    (hn : 2 ≤ n) (hRh : R.IsHomogeneous n) (hR : Irreducible R) (hHR : aeval H R = 0)
    (g : MvPolynomial (Fin 4) K) (P : Fin 4 → MvPolynomial (Fin 4) K)
    (hP : IsPrimitiveVec P) (hHP : H = fun i => g * P i) :
    ¬ ∀ i j, R ∣ X i * P j - X j * P i := by
  intro hcross
  obtain ⟨m, V, hHV, j, hj⟩ := exists_saturated_common_power R (by omega) hR.ne_zero hRh H hH0
  have hVh := homogeneous_vector_remove_power R hR.ne_zero hRh H V hH m hHV
  have hV := homogeneous_relation_remove_common_power R hR.ne_zero hRh H V m hHV hHR
  have hcrossV := primitive_cross_relations_remove_common_power R hR H P V g hP hHP m hHV hcross
  obtain ⟨W, hpoint⟩ := radial_cross_relations_presentation R V j (fun i => hcrossV j i)
  exact no_radial_coordinate_presentation R (by omega) hRh hR H V W hVh m hHV hV hdiv j
    (nonlinear_homogeneous_not_dvd_coordinate R hn hR.ne_zero hRh j) hj hpoint

/-- Apply the fixed-point exclusion to the actual irreducible image
equation of the original nilpotent rank-three map. -/
theorem ImageRelationWitness.primitive_map_not_radial [CharZero K]
    (H : Fin 4 → MvPolynomial (Fin 4) K) {d : ℕ} (hH : IsHomogMap H d)
    (hN : IsNilpotent (jac H)) (hrank : polyRank (jac H) = 3) (W : ImageRelationWitness H)
    (hnonlinear : 2 ≤ W.degree) (g : MvPolynomial (Fin 4) K)
    (P : Fin 4 → MvPolynomial (Fin 4) K) (hP : IsPrimitiveVec P) (hHP : H = fun i => g * P i) :
    ¬ ∀ i j, W.equation ∣ X i * P j - X j * P i := by
  have hH0 : H ≠ 0 := by
    intro hz
    have hJ : jac H = 0 := by
      funext i j
      change pderiv j (H i) = 0
      rw [hz]
      simp
    have hr0 : polyRank (jac H) = 0 := by rw [hJ]; simp [polyRank]
    omega
  have hdiv : divergence H = 0 := by
    rw [divergence_eq_trace]
    exact trace_jac_zero H hN
  exact primitive_map_not_radial_on_nonlinear_image H hH hH0 hdiv W.equation hnonlinear
    W.homogeneous W.irreducible W.vanishing g P hP hHP

/-- If the primitive map fixes the generic image in the algebraic
cross-coordinate sense, the image is linear and the components dependent. -/
theorem primitive_radial_image_forces_dependence [CharZero K]
    (H : Fin 4 → MvPolynomial (Fin 4) K) {d : ℕ} (hd : 0 < d) (hH : IsHomogMap H d)
    (hN : IsNilpotent (jac H)) (hrank : polyRank (jac H) = 3) (W : ImageRelationWitness H)
    (g : MvPolynomial (Fin 4) K) (P : Fin 4 → MvPolynomial (Fin 4) K)
    (hP : IsPrimitiveVec P) (hHP : H = fun i => g * P i)
    (hfixed : ∀ i j, W.equation ∣ X i * P j - X j * P i) : ComponentsDependent H := by
  by_cases he : W.degree = 1
  · exact W.dependent_of_degree_one H hd hH he
  · have htwo : 2 ≤ W.degree := by have hp := W.degree_pos; omega
    exact False.elim (W.primitive_map_not_radial H hH hN hrank htwo g P hP hHP hfixed)

end DimensionFourDependence
