import DimensionFourDependence.FiberPrimeDimension

/-! # The fiber prime has height two and is a component of the two equations -/

namespace DimensionFourDependence

open MvPolynomial

/-- A prime ideal containing two relatively prime elements, one nonzero,
has height at least two in a UFD. -/
theorem two_le_prime_height_of_relPrime_mem {R : Type*} [CommRing R] [IsDomain R]
    [UniqueFactorizationMonoid R] (I : Ideal R) [I.IsPrime]
    (p q : R) (hp0 : p ≠ 0) (hp : p ∈ I) (hq : q ∈ I) (hcop : IsRelPrime p q) :
    2 ≤ I.height := by
  by_contra h
  rcases Order.le_one_iff.mp (ENat.lt_two_iff.mp (lt_of_not_ge h)) with h0 | h1
  · have he : I = ⊥ := Ideal.height_eq_zero_iff_eq_bot.mp h0
    rw [he, Ideal.mem_bot] at hp
    exact hp0 hp
  · obtain ⟨r, hr⟩ := UniqueFactorizationMonoid.isPrincipal_of_height_eq_one h1
    have hrp : r ∣ p := Ideal.mem_span_singleton.mp (by simpa only [hr] using hp)
    have hrq : r ∣ q := Ideal.mem_span_singleton.mp (by simpa only [hr] using hq)
    have he : I = ⊤ := hr.trans (Ideal.span_singleton_eq_top.mpr (hcop hrp hrq))
    exact Ideal.IsPrime.ne_top' he

/-- A nonmaximal prime in affine three-space has height at most two. -/
theorem affine_three_prime_height_le_two {L : Type*} [Field L]
    (I : Ideal (MvPolynomial (Fin 3) L)) [I.IsPrime] (hnm : ¬ I.IsMaximal) : I.height ≤ 2 := by
  have hd : ringKrullDim (MvPolynomial (Fin 3) L) = 3 := by simp
  have : FiniteRingKrullDim (MvPolynomial (Fin 3) L) :=
    finiteRingKrullDim_iff_ne_bot_and_top.mpr ⟨by rw [hd]; simp, by
      rw [hd]
      change ((3 : ℕ∞) : WithBot ℕ∞) ≠ ⊤
      exact fun h => ENat.natCast_ne_top 3 (WithBot.coe_eq_top.mp h)⟩
  have hb : (I.height : WithBot ℕ∞) ≤ 3 := by
    simpa only [hd] using (Ideal.height_le_ringKrullDim_of_isPrime (I := I))
  have hle : I.height ≤ 3 := WithBot.coe_le_coe.mp hb
  have hne : I.height ≠ 3 := by
    intro he
    apply hnm
    apply Ideal.isMaximal_of_height_eq_ringKrullDim
    simp only [he, hd, WithBot.coe_ofNat]
  have hlt : I.height < 3 := lt_of_le_of_ne hle hne
  apply (ENat.lt_natCast_add_one_iff (n := 2)).mp
  convert hlt using 1
  norm_num

/-- A height-two prime containing relatively prime equations is a
minimal prime of their ideal: there is no smaller prime over the pair. -/
theorem prime_minimal_over_relPrime_pair {R : Type*} [CommRing R] [IsDomain R]
    [UniqueFactorizationMonoid R] [IsNoetherianRing R]
    (I : Ideal R) [I.IsPrime] (hheight : I.height = 2)
    (p q : R) (hp0 : p ≠ 0) (hp : p ∈ I) (hq : q ∈ I) (hcop : IsRelPrime p q) :
    I ∈ (Ideal.span ({p, q} : Set R)).minimalPrimes := by
  have hspan : Ideal.span ({p, q} : Set R) ≤ I := by
    apply Ideal.span_le.mpr
    intro z hz
    rcases hz with rfl | rfl
    · exact hp
    · exact hq
  refine ⟨⟨inferInstance, hspan⟩, ?_⟩
  intro J hJ hJI
  have : J.IsPrime := hJ.1
  have hpJ : p ∈ J := hJ.2 (Ideal.subset_span (by simp))
  have hqJ : q ∈ J := hJ.2 (Ideal.subset_span (by simp))
  have hge := two_le_prime_height_of_relPrime_mem J p q hp0 hpJ hqJ hcop
  have he : J = I := Ideal.eq_of_le_of_height_le J hJI (by simpa only [hheight] using hge)
  exact he.ge

variable {K : Type*} [Field K] [CharZero K]

/-- The actual prime of the projected generic fiber has height two. -/
theorem fiber_witness_prime_height_two
    (H : Fin 4 → FractionRing (MvPolynomial (Fin 4) K))
    (hN : IsNilpotent (rationalJacobian H)) (hrank : (rationalJacobian H).rank = 3)
    (W : CoprimeFiberEquationWitness H) :
    (fiberVanishingIdeal
      (L := coefficientField (K := K) (fun i : Fin 3 => H (W.chart i.castSucc)))
      (fun i : Fin 3 => rationalCoordinate (K := K) (W.chart i.castSucc))).height = 2 := by
  have hm := fiber_witness_equations_mem_prime H W.toFiberEquationWitness
  apply le_antisymm
  · exact affine_three_prime_height_le_two _ (fiber_witness_prime_not_isMaximal H hN hrank W.toFiberEquationWitness)
  · exact two_le_prime_height_of_relPrime_mem _ W.quadric W.cubic
      (fiber_witness_quadric_ne_zero H W.toFiberEquationWitness) hm.1 hm.2 W.coprime

/-- The actual projected fiber prime is a minimal prime of its two
relatively prime equations, giving the affine irreducible-component assertion. -/
theorem fiber_witness_prime_minimal_over_equations
    (H : Fin 4 → FractionRing (MvPolynomial (Fin 4) K))
    (hN : IsNilpotent (rationalJacobian H)) (hrank : (rationalJacobian H).rank = 3)
    (W : CoprimeFiberEquationWitness H) :
    fiberVanishingIdeal
      (L := coefficientField (K := K) (fun i : Fin 3 => H (W.chart i.castSucc)))
      (fun i : Fin 3 => rationalCoordinate (K := K) (W.chart i.castSucc)) ∈
        (Ideal.span ({W.quadric, W.cubic} : Set (MvPolynomial (Fin 3)
          (coefficientField (K := K) (fun i : Fin 3 => H (W.chart i.castSucc)))))).minimalPrimes := by
  have hm := fiber_witness_equations_mem_prime H W.toFiberEquationWitness
  exact prime_minimal_over_relPrime_pair _ (fiber_witness_prime_height_two H hN hrank W)
    W.quadric W.cubic (fiber_witness_quadric_ne_zero H W.toFiberEquationWitness) hm.1 hm.2 W.coprime

end DimensionFourDependence
