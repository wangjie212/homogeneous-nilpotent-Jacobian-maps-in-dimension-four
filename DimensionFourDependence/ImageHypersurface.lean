import DimensionFourDependence.ImageRelationHeight
import DimensionFourDependence.ConstantPlaneNormal

/-! # The defining homogeneous hypersurface of a rank-three image

The relation prime has height one. Its irreducible relation therefore
generates the entire prime, and every polynomial vanishing on the image
is divisible by this equation. The equation is linear exactly when the
components are linearly dependent.
-/

namespace DimensionFourDependence

open MvPolynomial

variable {K : Type*} [Field K]

/-- The actual prime of polynomial equations of the affine image. -/
noncomputable def imageRelationIdeal (H : Fin 4 → MvPolynomial (Fin 4) K) :
    Ideal (MvPolynomial (Fin 4) K) := RingHom.ker (aeval H)

@[instance]
theorem imageRelationIdeal_isPrime (H : Fin 4 → MvPolynomial (Fin 4) K) :
    (imageRelationIdeal H).IsPrime := RingHom.ker_isPrime (aeval H)

/-- Passing to the rational source field preserves all output relations. -/
theorem imageRelationIdeal_eq_rational_relations (H : Fin 4 → MvPolynomial (Fin 4) K) :
    imageRelationIdeal H = fiberVanishingIdeal (L := K)
      (fun i => algebraMap (MvPolynomial (Fin 4) K) (FractionRing (MvPolynomial (Fin 4) K)) (H i)) := by
  ext P
  change aeval H P = 0 ↔ aeval (fun i => algebraMap (MvPolynomial (Fin 4) K)
    (FractionRing (MvPolynomial (Fin 4) K)) (H i)) P = 0
  rw [← aeval_polynomial_to_fraction]
  constructor
  · intro h
    rw [h, map_zero]
  · intro h
    apply IsFractionRing.injective (MvPolynomial (Fin 4) K) (FractionRing (MvPolynomial (Fin 4) K))
    simpa only [map_zero] using h

/-- The full image relation prime has height at most one in rank three. -/
theorem imageRelationIdeal_height_le_one [CharZero K]
    (H : Fin 4 → MvPolynomial (Fin 4) K) (hrank : polyRank (jac H) = 3) :
    (imageRelationIdeal H).height ≤ 1 := by
  classical
  let Q : Fin 4 → FractionRing (MvPolynomial (Fin 4) K) :=
    fun i => algebraMap (MvPolynomial (Fin 4) K) _ (H i)
  have hrQ : (rationalJacobian Q).rank = 3 := by
    rw [rationalJacobian_polynomial H]
    exact hrank
  obtain ⟨s, hs, hY, _⟩ := exists_independent_output_triple Q hrQ
  obtain ⟨p, hp⟩ := Equiv.Perm.exists_extending_pair Fin.castSucc s (Fin.castSucc_injective 3) hs
  have hYs : (fun i : Fin 3 => Q (p i.castSucc)) = fun i => Q (s i) := by
    funext i
    rw [hp]
  rw [imageRelationIdeal_eq_rational_relations]
  apply output_relation_prime_height_le_one Q p
  rwa [hYs]

/-- The nonzero relation makes the rank-three image prime have height exactly one. -/
theorem ImageRelationWitness.ideal_height_one [CharZero K]
    (H : Fin 4 → MvPolynomial (Fin 4) K) (hrank : polyRank (jac H) = 3)
    (W : ImageRelationWitness H) : (imageRelationIdeal H).height = 1 := by
  apply le_antisymm (imageRelationIdeal_height_le_one H hrank)
  apply Order.one_le_iff_ne_zero.mpr
  intro hz
  have he := Ideal.height_eq_zero_iff_eq_bot.mp hz
  have hm : W.equation ∈ imageRelationIdeal H := W.vanishing
  rw [he, Ideal.mem_bot] at hm
  exact W.irreducible.ne_zero hm

/-- The constructed irreducible relation is the defining equation of the image. -/
theorem ImageRelationWitness.ideal_eq_span [CharZero K]
    (H : Fin 4 → MvPolynomial (Fin 4) K) (hrank : polyRank (jac H) = 3)
    (W : ImageRelationWitness H) : imageRelationIdeal H = Ideal.span {W.equation} := by
  exact Ideal.eq_span_singleton_of_height_eq_one (W.ideal_height_one H hrank)
    W.vanishing W.irreducible.prime

/-- Every image equation, with no homogeneity restriction, is a multiple
of the checked homogeneous irreducible defining equation. -/
theorem ImageRelationWitness.relation_iff_dvd [CharZero K]
    (H : Fin 4 → MvPolynomial (Fin 4) K) (hrank : polyRank (jac H) = 3)
    (W : ImageRelationWitness H) (P : MvPolynomial (Fin 4) K) :
    aeval H P = 0 ↔ W.equation ∣ P := by
  change P ∈ imageRelationIdeal H ↔ _
  rw [W.ideal_eq_span H hrank, Ideal.mem_span_singleton]

/-- A linear image equation gives a constant component relation. -/
theorem ImageRelationWitness.dependent_of_degree_one [CharZero K]
    (H : Fin 4 → MvPolynomial (Fin 4) K) {d : ℕ} (hd : 0 < d) (hH : IsHomogMap H d)
    (W : ImageRelationWitness H) (he : W.degree = 1) : ComponentsDependent H := by
  apply dependent_of_left_normal_deg_le_one H (imageRelationNormal H W.equation)
    (by omega) hH W.normal_ne_zero (β := 0) _ (by norm_num) (W.left_kernel H)
  simpa only [he, Nat.sub_self, mul_zero] using W.normal_homogeneous H hH

/-- Conversely, a constant component relation makes the defining image
equation linear. This is the plane-image/dependence equivalence. -/
theorem ImageRelationWitness.degree_one_of_dependent [CharZero K]
    (H : Fin 4 → MvPolynomial (Fin 4) K) (hrank : polyRank (jac H) = 3)
    (W : ImageRelationWitness H) (hdep : ComponentsDependent H) : W.degree = 1 := by
  obtain ⟨c, hc, hrel⟩ := hdep
  let L : MvPolynomial (Fin 4) K := ∑ i, C (c i) * X i
  have hLh : L.IsHomogeneous 1 :=
    IsHomogeneous.sum _ _ _ fun i _ => isHomogeneous_C_mul_X (c i) i
  have hL0 : L ≠ 0 := by
    intro hz
    apply hc
    funext i
    have ht := congrArg (pderiv i) hz
    simpa [L, map_sum, Derivation.leibniz, Pi.single_apply] using ht
  have hLe : aeval H L = 0 := by
    simpa [L, MvPolynomial.smul_eq_C_mul] using hrel
  obtain ⟨q, hq⟩ := (W.relation_iff_dvd H hrank L).mp hLe
  have hq0 : q ≠ 0 := by
    intro hz
    apply hL0
    rw [hq, hz, mul_zero]
  have hdeg := congrArg MvPolynomial.totalDegree hq
  rw [hLh.totalDegree hL0,
    totalDegree_mul_of_isDomain W.irreducible.ne_zero hq0,
    W.homogeneous.totalDegree W.irreducible.ne_zero] at hdeg
  have hp := W.degree_pos
  omega

end DimensionFourDependence
