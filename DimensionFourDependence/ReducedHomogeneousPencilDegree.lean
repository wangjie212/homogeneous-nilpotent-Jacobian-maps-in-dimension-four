import DimensionFourDependence.ClosedGaussPencilDegreeBound

/-! # Every reduced presentation of the actual Gauss parameter has the required degree bound -/

namespace DimensionFourDependence

open MvPolynomial

variable {K : Type*} [Field K]

/-- Equality of rational quotients forces the denominator of a
reduced presentation to divide the denominator of every presentation. -/
theorem reduced_source_fraction_denominator_dvd
    (p q p' q' : MvPolynomial (Fin 4) K) (hq : q ≠ 0) (hq' : q' ≠ 0)
    (hrel : IsRelPrime p q)
    (heq : algebraMap _ (FractionRing (MvPolynomial (Fin 4) K)) p /
        algebraMap _ (FractionRing (MvPolynomial (Fin 4) K)) q =
      algebraMap _ (FractionRing (MvPolynomial (Fin 4) K)) p' /
        algebraMap _ (FractionRing (MvPolynomial (Fin 4) K)) q') : q ∣ q' := by
  have hqF := (IsFractionRing.injective (MvPolynomial (Fin 4) K)
    (FractionRing (MvPolynomial (Fin 4) K))).ne hq
  have hqF' := (IsFractionRing.injective (MvPolynomial (Fin 4) K)
    (FractionRing (MvPolynomial (Fin 4) K))).ne hq'
  have hcross : p * q' = p' * q := by
    apply IsFractionRing.injective (MvPolynomial (Fin 4) K) (FractionRing (MvPolynomial (Fin 4) K))
    simpa only [map_mul, map_zero] using (div_eq_div_iff (by simpa using hqF) (by simpa using hqF')).mp heq
  apply hrel.symm.dvd_of_dvd_mul_left
  rw [hcross]
  exact dvd_mul_left q p'

/-- The degree of a reduced homogeneous quotient is at most the
degree of any homogeneous presentation of the same source function. -/
theorem reduced_homogeneous_source_fraction_degree_le
    (p q p' q' : MvPolynomial (Fin 4) K) {D D' : ℕ}
    (hq : q ≠ 0) (hq' : q' ≠ 0) (hrel : IsRelPrime p q)
    (hqH : q.IsHomogeneous D) (hqH' : q'.IsHomogeneous D')
    (heq : algebraMap _ (FractionRing (MvPolynomial (Fin 4) K)) p /
        algebraMap _ (FractionRing (MvPolynomial (Fin 4) K)) q =
      algebraMap _ (FractionRing (MvPolynomial (Fin 4) K)) p' /
        algebraMap _ (FractionRing (MvPolynomial (Fin 4) K)) q') : D ≤ D' := by
  have hdiv := reduced_source_fraction_denominator_dvd p q p' q' hq hq' hrel heq
  have hb := totalDegree_le_of_dvd_of_isDomain hdiv hq'
  rwa [hqH.totalDegree hq, hqH'.totalDegree hq'] at hb

variable [CharZero K]

/-- Every given reduced original-coordinate presentation of the
actual closed Gauss parameter has degree at most the primitive map
degree; the bound is independent of the chosen presentation. -/
theorem actual_closed_gauss_given_parameter_pencil_degree_le_primitive_degree
    (H : Fin 4 → MvPolynomial (Fin 4) K) {d : ℕ} (hd : 0 < d) (hH : IsHomogMap H d)
    (hind : ¬ ComponentsDependent H) (I : ImageRelationWitness H)
    (e : RatFunc K ≃ₐ[K] closedGaussParameterField H I)
    (g : MvPolynomial (Fin 4) K) (hg : g ≠ 0)
    (P : Fin 4 → MvPolynomial (Fin 4) K) {fdeg : ℕ} (hP : IsHomogMap P fdeg)
    (hHP : H = fun i => g * P i)
    (p q : MvPolynomial (Fin 4) K) {D : ℕ}
    (hq : q ≠ 0) (hrel : IsRelPrime p q) (hqH : q.IsHomogeneous D)
    (ht : closedGaussParameterSourceHom H I e RatFunc.X =
      algebraMap _ (FractionRing (MvPolynomial (Fin 4) K)) p /
        algebraMap _ (FractionRing (MvPolynomial (Fin 4) K)) q) : D ≤ fdeg := by
  obtain ⟨p', q', D', _hD', hb, _hp', hq', _hpH', hqH', _hrel', ht'⟩ :=
    actual_closed_gauss_parameter_pencil_degree_le_primitive_degree H hd hH hind I e g hg P hP hHP
  exact (reduced_homogeneous_source_fraction_degree_le p q p' q' hq hq' hrel hqH hqH'
    (ht.symm.trans ht')).trans hb

/-- For every given reduced Gauss pencil, the original homogeneous
map and its factorization supply D <= d-deg(g); no numerical degree
bound on the pencil is assumed. -/
theorem actual_closed_gauss_given_parameter_pencil_degree_le_degree_sub_common_factor
    (H : Fin 4 → MvPolynomial (Fin 4) K) {d : ℕ} (hd : 0 < d) (hH : IsHomogMap H d)
    (hind : ¬ ComponentsDependent H) (I : ImageRelationWitness H)
    (e : RatFunc K ≃ₐ[K] closedGaussParameterField H I)
    (g : MvPolynomial (Fin 4) K) (hg : g ≠ 0)
    (P : Fin 4 → MvPolynomial (Fin 4) K) {fdeg : ℕ} (hP : IsHomogMap P fdeg)
    (hHP : H = fun i => g * P i)
    (p q : MvPolynomial (Fin 4) K) {D : ℕ}
    (hq : q ≠ 0) (hrel : IsRelPrime p q) (hqH : q.IsHomogeneous D)
    (ht : closedGaussParameterSourceHom H I e RatFunc.X =
      algebraMap _ (FractionRing (MvPolynomial (Fin 4) K)) p /
        algebraMap _ (FractionRing (MvPolynomial (Fin 4) K)) q) : D ≤ d - g.totalDegree := by
  have hH0 : H 0 ≠ 0 := (linearIndependent_of_componentsIndependent H hind).ne_zero 0
  have hP0 : P 0 ≠ 0 := by
    intro hzero
    apply hH0
    simpa only [hzero, mul_zero] using congrFun hHP 0
  have hdeg : d = g.totalDegree + fdeg := by
    have heq := congrArg MvPolynomial.totalDegree (congrFun hHP 0)
    rw [(hH 0).totalDegree hH0, totalDegree_mul_of_isDomain hg hP0, (hP 0).totalDegree hP0] at heq
    exact heq
  have hb := actual_closed_gauss_given_parameter_pencil_degree_le_primitive_degree
    H hd hH hind I e g hg P hP hHP p q hq hrel hqH ht
  omega

end DimensionFourDependence
