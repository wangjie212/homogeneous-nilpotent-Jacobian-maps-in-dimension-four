import DimensionFourDependence.CoprimeBaseGenericAvoidance
import DimensionFourDependence.RadialCoordinateFieldDimension
import DimensionFourDependence.IndependentScaleHomogeneousValues
import DimensionFourDependence.GeneratedPointPrimeDimension

/-! # A coprime ternary homogeneous base has only algebraic projective directions -/

namespace DimensionFourDependence

open MvPolynomial

universe u

set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 100000

variable {K A : Type u} [Field K] [CommRing A] [IsDomain A] [Algebra K A]
    [Algebra.FiniteType K A] [UniqueFactorizationMonoid A]

/-- A relatively prime pair in a three-dimensional factorial affine
domain leaves a prime quotient of transcendence degree below two. -/
theorem relPrime_pair_prime_quotient_trdeg_lt_two
    (hA : Algebra.trdeg K A = 3) (P : Ideal A) [P.IsPrime]
    (p q : A) (hp0 : p ≠ 0) (hrel : IsRelPrime p q) (hp : p ∈ P) (hq : q ∈ P) :
    Algebra.trdeg K (A ⧸ P) < 2 := by
  classical
  let : IsNoetherianRing A := Algebra.FiniteType.isNoetherianRing K A
  by_contra hn
  have hge : 2 ≤ Algebra.trdeg K (A ⧸ P) := le_of_not_gt hn
  have hPne : P ≠ ⊥ := by
    intro he
    exact hp0 (Ideal.mem_bot.mp (he ▸ hp))
  obtain ⟨δ, hδP, hδprime⟩ := Ideal.IsPrime.exists_mem_prime_of_ne_bot
    (inferInstance : P.IsPrime) hPne
  let Q : Ideal A := Ideal.span {δ}
  let : Q.IsPrime := Ideal.isPrime_span_singleton_of_prime hδprime
  have hQP : Q ≤ P := Ideal.span_le.mpr (Set.singleton_subset_iff.mpr hδP)
  have hQne : Q ≠ ⊥ := by
    intro he
    exact hδprime.ne_zero (Ideal.mem_bot.mp
      (he ▸ (Ideal.subset_span (Set.mem_singleton δ))))
  have hlt : Algebra.trdeg K (A ⧸ Q) < 3 :=
    (prime_quotient_trdeg_lt (K' := K) Q hQne
      (trdeg_lt_aleph0_of_finiteType (R := K) (S := A))).trans_eq hA
  have hle : Algebra.trdeg K (A ⧸ Q) ≤ 2 :=
    (Cardinal.lt_natCast_add_one_iff (n := 2)).mp (by convert hlt using 1; norm_num)
  let g := Ideal.Quotient.factorₐ K hQP
  have hgs : Function.Surjective g := Ideal.Quotient.factor_surjective hQP
  have hPQ : Algebra.trdeg K (A ⧸ P) ≤ Algebra.trdeg K (A ⧸ Q) :=
    trdeg_le_of_surjective g hgs
  have heq : Algebra.trdeg K (A ⧸ Q) = Algebra.trdeg K (A ⧸ P) :=
    le_antisymm (hle.trans hge) hPQ
  have hginj := surjective_algHom_injective_of_trdeg_eq g hgs
    (trdeg_lt_aleph0_of_finiteType (R := K) (S := A ⧸ Q)) heq
  have hPQ' : P ≤ Q := by
    intro a ha
    apply Ideal.Quotient.eq_zero_iff_mem.mp
    apply hginj
    exact (Ideal.Quotient.eq_zero_iff_mem.mpr ha).trans (map_zero g).symm
  exact hδprime.not_isUnit (hrel
    (Ideal.mem_span_singleton.mp (hPQ' hp)) (Ideal.mem_span_singleton.mp (hPQ' hq)))

variable [CharZero K] {E : Type u} [Field E] [Algebra K E]

/-- Every extension-valued projective common zero of a coprime
original ternary homogeneous pair has zero-dimensional ratio field.
An independent radial variable turns a nonconstant direction into a
two-dimensional affine point, contradicting the coprime base bound. -/
theorem coprime_ternary_homogeneous_common_zero_projective_trdeg_zero
    (p q : MvPolynomial (Fin 3) K) (hp0 : p ≠ 0) (hrel : IsRelPrime p q)
    {a b : ℕ} (hp : p.IsHomogeneous a) (hq : q.IsHomogeneous b)
    (v : Fin 3 → E) (j : Fin 3) (hj : v j ≠ 0)
    (hvp : aeval v p = 0) (hvq : aeval v q = 0) :
    Algebra.trdeg K (projectiveRatioField (K := K) v j) = 0 := by
  by_contra hdim
  let y : Fin 3 → RatFunc E := fun i => RatFunc.X * RatFunc.C (v i)
  let P := fiberVanishingIdeal (L := K) y
  have hpP : p ∈ P := by
    change aeval (fun i => (RatFunc.X : RatFunc E) * RatFunc.C (v i)) p = 0
    rw [independent_scale_homogeneous_polynomial_value p hp, hvp, map_zero, mul_zero]
  have hqP : q ∈ P := by
    change aeval (fun i => (RatFunc.X : RatFunc E) * RatFunc.C (v i)) q = 0
    rw [independent_scale_homogeneous_polynomial_value q hq, hvq, map_zero, mul_zero]
  have hlt := relPrime_pair_prime_quotient_trdeg_lt_two
    (K := K) (A := MvPolynomial (Fin 3) K) (by simp) P p q hp0 hrel hpP hqP
  have hge := nonconstant_direction_independent_radial_field_dimension_ge_two v j hj hdim
  rw [coordinate_relation_quotient_trdeg_eq_generated_point_field y] at hlt
  exact not_le_of_gt hlt hge

/-- The actual normalized coordinates of each projective base point
are algebraic over the original field, before any algebraic closure. -/
theorem coprime_ternary_homogeneous_common_zero_ratios_algebraic
    (p q : MvPolynomial (Fin 3) K) (hp0 : p ≠ 0) (hrel : IsRelPrime p q)
    {a b : ℕ} (hp : p.IsHomogeneous a) (hq : q.IsHomogeneous b)
    (v : Fin 3 → E) (j : Fin 3) (hj : v j ≠ 0)
    (hvp : aeval v p = 0) (hvq : aeval v q = 0) :
    ∀ i : Fin 3, IsAlgebraic K (v i / v j) :=
  (projective_ratio_dimension_zero_iff_coordinate_algebraic v j).mp
    (coprime_ternary_homogeneous_common_zero_projective_trdeg_zero p q hp0 hrel hp hq v j hj hvp hvq)

end DimensionFourDependence
