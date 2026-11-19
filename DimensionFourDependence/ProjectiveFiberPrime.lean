import DimensionFourDependence.ProjectiveCone

/-! # The generic projective fiber is a component of the intersection

The cone prime is strictly below the chart prime. The latter is nonmaximal
in a four-variable polynomial ring, so the cone has height at most two.
Relative primality supplies the reverse inequality and the minimal-prime result.
-/

namespace DimensionFourDependence

open MvPolynomial

variable {L F σ : Type*} [Field L] [Field F] [Algebra L F]

/-- Zariski's lemma excludes maximality when the coordinates generate
a transcendental extension. The index set can be any finite type. -/
theorem aeval_kernel_not_isMaximal [Finite σ] (x : σ → F)
    (hx : IntermediateField.adjoin L (Set.range x) = ⊤) (htr : Algebra.trdeg L F ≠ 0) :
    ¬ (RingHom.ker (aeval x : MvPolynomial σ L →ₐ[L] F)).IsMaximal := by
  intro hm
  let I := RingHom.ker (aeval x : MvPolynomial σ L →ₐ[L] F)
  let : I.IsMaximal := hm
  let : Field (MvPolynomial σ L ⧸ I) := Ideal.Quotient.field _
  have : Module.Finite L (MvPolynomial σ L ⧸ I) :=
    finite_of_finite_type_of_isJacobsonRing L _
  have hAlg (i : σ) : IsAlgebraic L (x i) := by
    have ha := IsAlgebraic.of_finite L (Ideal.Quotient.mk I (X i))
    have hb := ha.algHom (Ideal.kerLiftAlg (aeval x : MvPolynomial σ L →ₐ[L] F))
    change IsAlgebraic L ((aeval x) (X i)) at hb
    simpa only [aeval_X] using hb
  have hle : IntermediateField.adjoin L (Set.range x) ≤ algebraicClosure L F := by
    apply IntermediateField.adjoin_le_iff.mpr
    rintro _ ⟨i, rfl⟩
    exact mem_algebraicClosure_iff.mpr (hAlg i)
  rw [hx] at hle
  have : Algebra.IsAlgebraic L F := ⟨fun z => mem_algebraicClosure_iff.mp (hle (by trivial))⟩
  exact htr trdeg_eq_zero

/-- A nonmaximal prime in four-dimensional affine space has height at most three. -/
theorem affine_four_prime_height_le_three
    (I : Ideal (MvPolynomial (Option (Fin 3)) L)) [I.IsPrime] (hnm : ¬ I.IsMaximal) :
    I.height ≤ 3 := by
  have hd : ringKrullDim (MvPolynomial (Option (Fin 3)) L) = 4 := by simp
  have : FiniteRingKrullDim (MvPolynomial (Option (Fin 3)) L) :=
    finiteRingKrullDim_iff_ne_bot_and_top.mpr ⟨by rw [hd]; simp, by
      rw [hd]
      change ((4 : ℕ∞) : WithBot ℕ∞) ≠ ⊤
      exact fun h => ENat.natCast_ne_top 4 (WithBot.coe_eq_top.mp h)⟩
  have hb : (I.height : WithBot ℕ∞) ≤ 4 := by
    simpa only [hd] using (Ideal.height_le_ringKrullDim_of_isPrime (I := I))
  have hle : I.height ≤ 4 := WithBot.coe_le_coe.mp hb
  have hne : I.height ≠ 4 := by
    intro he
    apply hnm
    apply Ideal.isMaximal_of_height_eq_ringKrullDim
    simp only [he, hd, WithBot.coe_ofNat]
  apply (ENat.lt_natCast_add_one_iff (n := 3)).mp
  convert lt_of_le_of_ne hle hne using 1
  norm_num

/-- The homogeneous closure prime has height at most two whenever the
affine coordinates generate a transcendental extension. -/
theorem projectiveConeIdeal_height_le_two (x : Fin 3 → F)
    (hx : IntermediateField.adjoin L (Set.range x) = ⊤) (htr : Algebra.trdeg L F ≠ 0) :
    (projectiveConeIdeal (L := L) x).height ≤ 2 := by
  let I := RingHom.ker
    (aeval (fun j : Option (Fin 3) => j.elim 1 x) : MvPolynomial (Option (Fin 3)) L →ₐ[L] F)
  have : I.IsPrime := RingHom.ker_isPrime _
  have hc : IntermediateField.adjoin L (Set.range (fun j : Option (Fin 3) => j.elim 1 x)) = ⊤ := by
    apply top_unique
    rw [← hx]
    apply IntermediateField.adjoin_le_iff.mpr
    rintro _ ⟨i, rfl⟩
    apply IntermediateField.subset_adjoin
    exact ⟨some i, rfl⟩
  have hb : I.height ≤ 3 := affine_four_prime_height_le_three I
    (aeval_kernel_not_isMaximal _ hc htr)
  have hs : (projectiveConeIdeal (L := L) x).height < I.height :=
    Ideal.height_strict_mono_of_isPrime (projectiveConeIdeal_lt_chart x)
  apply (ENat.lt_natCast_add_one_iff (n := 2)).mp
  convert hs.trans_le hb using 1
  norm_num

/-- On the standard affine chart the homogeneous prime recovers precisely
the original affine relation ideal. -/
theorem projectiveConeIdeal_dehomogenize (x : Fin 3 → F) :
    Ideal.map (projectiveDehomogenize (R := L)).toRingHom (projectiveConeIdeal (L := L) x) =
      fiberVanishingIdeal (L := L) x := by
  apply le_antisymm
  · apply Ideal.map_le_iff_le_comap.mpr
    intro p hp
    change aeval x (projectiveDehomogenize p) = 0
    rw [← aeval_projectiveDehomogenize, ← projectiveConeMap_eval_one]
    change projectiveConeMap (L := L) x p = 0 at hp
    rw [hp, Polynomial.eval_zero]
  · intro p hp
    have hm : projectiveHomogenize p p.totalDegree ∈ projectiveConeIdeal (L := L) x := by
      apply (projectiveConeIdeal_mem_of_isHomogeneous x
        (projectiveHomogenize_isHomogeneous p p.totalDegree le_rfl)).mpr
      rw [projectiveHomogenize_aeval_chart]
      exact hp
    have ht := Ideal.mem_map_of_mem (projectiveDehomogenize (R := L)).toRingHom hm
    simpa only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, projectiveDehomogenize_homogenize] using ht

variable {K : Type*} [Field K] [CharZero K]

omit [CharZero K] in
/-- Both homogeneous fiber equations belong to the actual closure prime. -/
theorem projective_fiber_witness_equations_mem_prime
    (H : Fin 4 → FractionRing (MvPolynomial (Fin 4) K)) (W : ProjectiveFiberEquationWitness H) :
    W.quadric ∈ projectiveConeIdeal
      (L := coefficientField (K := K) (fun i : Fin 3 => H (W.affine.chart i.castSucc)))
      (fun i : Fin 3 => rationalCoordinate (K := K) (W.affine.chart i.castSucc)) ∧
    W.cubic ∈ projectiveConeIdeal
      (L := coefficientField (K := K) (fun i : Fin 3 => H (W.affine.chart i.castSucc)))
      (fun i : Fin 3 => rationalCoordinate (K := K) (W.affine.chart i.castSucc)) := by
  exact ⟨(projectiveConeIdeal_mem_of_isHomogeneous _ W.quadric_homogeneous).mpr W.quadric_zero,
    (projectiveConeIdeal_mem_of_isHomogeneous _ W.cubic_homogeneous).mpr W.cubic_zero⟩

/-- The homogeneous prime of the actual generic projective fiber has height two. -/
theorem projective_fiber_witness_prime_height_two
    (H : Fin 4 → FractionRing (MvPolynomial (Fin 4) K))
    (hN : IsNilpotent (rationalJacobian H)) (hrank : (rationalJacobian H).rank = 3)
    (W : ProjectiveFiberEquationWitness H) :
    (projectiveConeIdeal
      (L := coefficientField (K := K) (fun i : Fin 3 => H (W.affine.chart i.castSucc)))
      (fun i : Fin 3 => rationalCoordinate (K := K) (W.affine.chart i.castSucc))).height = 2 := by
  have hm := projective_fiber_witness_equations_mem_prime H W
  apply le_antisymm
  · apply projectiveConeIdeal_height_le_two _
      (fiber_witness_coordinate_field_eq_top H W.affine.toFiberEquationWitness)
    rw [fiber_witness_trdeg_eq_one H hN hrank W.affine.toFiberEquationWitness]
    exact one_ne_zero
  · exact two_le_prime_height_of_relPrime_mem _ W.quadric W.cubic
      W.quadric_ne_zero hm.1 hm.2 W.coprime

/-- The closure prime is a minimal prime over the two homogeneous equations.
This is the projective intersection-component statement over the actual coefficient field. -/
theorem projective_fiber_witness_prime_minimal_over_equations
    (H : Fin 4 → FractionRing (MvPolynomial (Fin 4) K))
    (hN : IsNilpotent (rationalJacobian H)) (hrank : (rationalJacobian H).rank = 3)
    (W : ProjectiveFiberEquationWitness H) :
    projectiveConeIdeal
      (L := coefficientField (K := K) (fun i : Fin 3 => H (W.affine.chart i.castSucc)))
      (fun i : Fin 3 => rationalCoordinate (K := K) (W.affine.chart i.castSucc)) ∈
        (Ideal.span ({W.quadric, W.cubic} : Set (MvPolynomial (Option (Fin 3))
          (coefficientField (K := K) (fun i : Fin 3 => H (W.affine.chart i.castSucc)))))).minimalPrimes := by
  have hm := projective_fiber_witness_equations_mem_prime H W
  exact prime_minimal_over_relPrime_pair _ (projective_fiber_witness_prime_height_two H hN hrank W)
    W.quadric W.cubic W.quadric_ne_zero hm.1 hm.2 W.coprime

end DimensionFourDependence
