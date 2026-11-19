import DimensionFourDependence.HomogeneousDehomogenize
import DimensionFourDependence.RationalPointLocalModel

/-! # Clearing the actual affine-chart and local-ring denominators

Every relation in the dehomogenized homogeneous ideal lifts to one
homogeneous original relation. A homogeneous form lying in that chart
ideal therefore lies in the original ideal after multiplication by a
power of the chart coordinate. If its image in the actual origin
localization vanishes, a homogeneous equation nonzero at that point
clears all denominators in the original homogeneous ring.
-/

namespace DimensionFourDependence

open MvPolynomial

attribute [local instance] MvPolynomial.gradedAlgebra

variable {F sigma : Type*} [Field F]

/-- The actual affine-chart ideal obtained by setting the homogeneous
chart coordinate equal to one. -/
noncomputable def projectiveDehomogenizedIdeal
    (I : Ideal (MvPolynomial (Option sigma) F)) : Ideal (MvPolynomial sigma F) :=
  I.map (projectiveDehomogenize (R := F) (σ := sigma)).toRingHom

/-- Every element of the actual dehomogenized ideal has a homogeneous
lift inside the original homogeneous ideal. -/
theorem projectiveDehomogenizedIdeal_homogeneous_lift
    (I : Ideal (MvPolynomial (Option sigma) F))
    (hI : I.IsHomogeneous (homogeneousSubmodule (Option sigma) F))
    (p : MvPolynomial sigma F) (hp : p ∈ projectiveDehomogenizedIdeal I) :
    ∃ d : ℕ, ∃ Q : MvPolynomial (Option sigma) F,
      Q.IsHomogeneous d ∧ Q ∈ I ∧ projectiveDehomogenize Q = p := by
  classical
  have hsurj : Function.Surjective (projectiveDehomogenize (R := F) (σ := sigma)) :=
    fun q => ⟨rename some q, projectiveDehomogenize_rename q⟩
  obtain ⟨P, hPI, hP⟩ := (Ideal.mem_map_iff_of_surjective
    (projectiveDehomogenize (R := F) (σ := sigma)).toRingHom hsurj).mp hp
  let d := P.totalDegree
  let Q : MvPolynomial (Option sigma) F := ∑ k ∈ Finset.range (d + 1),
    X none ^ (d - k) * homogeneousComponent k P
  have hQ : Q.IsHomogeneous d := by
    apply IsHomogeneous.sum
    intro k hk
    have hk' : k ≤ d := by have := Finset.mem_range.mp hk; omega
    have hh := (isHomogeneous_X_pow (R := F) (none : Option sigma) (d - k)).mul
      (homogeneousComponent_isHomogeneous k P)
    convert hh using 1
    omega
  have hQI : Q ∈ I := by
    apply I.sum_mem
    intro k _
    exact I.mul_mem_left _ (homogeneousComponent_mem_of_mem hI hPI k)
  refine ⟨d, Q, hQ, hQI, ?_⟩
  change projectiveDehomogenize (∑ k ∈ Finset.range (P.totalDegree + 1),
    X none ^ (P.totalDegree - k) * homogeneousComponent k P) = p
  simp only [map_sum, map_mul, map_pow, projectiveDehomogenize_X_none, one_pow, one_mul]
  rw [← map_sum, sum_homogeneousComponent]
  exact hP

/-- A homogeneous form belongs to the actual chart ideal precisely
when a power of the chart coordinate puts it in the original ideal. -/
theorem homogeneous_dehomogenized_ideal_membership_iff
    (I : Ideal (MvPolynomial (Option sigma) F))
    (hI : I.IsHomogeneous (homogeneousSubmodule (Option sigma) F))
    (P : MvPolynomial (Option sigma) F) {n : ℕ} (hP : P.IsHomogeneous n) :
    projectiveDehomogenize P ∈ projectiveDehomogenizedIdeal I ↔
      ∃ k : ℕ, X none ^ k * P ∈ I := by
  constructor
  · intro hp
    obtain ⟨d, Q, hQ, hQI, he⟩ :=
      projectiveDehomogenizedIdeal_homogeneous_lift I hI _ hp
    have heq : X none ^ d * P = X none ^ n * Q := by
      apply homogeneous_dehomogenize_injective _ _
        ((isHomogeneous_X_pow (R := F) (none : Option sigma) d).mul hP)
      · simpa only [Nat.add_comm] using
          (isHomogeneous_X_pow (R := F) (none : Option sigma) n).mul hQ
      · simp only [map_mul, map_pow, projectiveDehomogenize_X_none, one_pow, one_mul, he]
    exact ⟨d, heq ▸ I.mul_mem_left _ hQI⟩
  · rintro ⟨k, hk⟩
    have hm := Ideal.mem_map_of_mem (projectiveDehomogenize (R := F) (σ := sigma)).toRingHom hk
    change projectiveDehomogenize (X none ^ k * P) ∈ projectiveDehomogenizedIdeal I at hm
    simpa only [map_mul, map_pow, projectiveDehomogenize_X_none, one_pow, one_mul] using hm

/-- Vanishing in the actual origin localization is cleared by a
homogeneous original equation nonzero at the specified chart point. -/
theorem origin_local_dehomogenized_vanishing_homogeneous_denominator
    (I : Ideal (MvPolynomial (Option sigma) F))
    (hI : I.IsHomogeneous (homogeneousSubmodule (Option sigma) F))
    (hJ : projectiveDehomogenizedIdeal I ≤ RingHom.ker (aeval (fun _ : sigma => (0 : F))).toRingHom)
    (P : MvPolynomial (Option sigma) F) {n : ℕ} (hP : P.IsHomogeneous n)
    (hzero : zeroPointLocalPolynomialHom (projectiveDehomogenizedIdeal I) hJ
      (projectiveDehomogenize P) = 0) :
    ∃ d : ℕ, ∃ S : MvPolynomial (Option sigma) F,
      S.IsHomogeneous d ∧ aeval (fun j : Option sigma => j.elim 1 (fun _ => (0 : F))) S ≠ 0 ∧
        S * P ∈ I := by
  let J := projectiveDehomogenizedIdeal I
  let q := zeroPointQuotientPrime J hJ
  change algebraMap (MvPolynomial sigma F ⧸ J) (Localization.AtPrime q)
    (Ideal.Quotient.mk J (projectiveDehomogenize P)) = 0 at hzero
  obtain ⟨t, ht⟩ := (IsLocalization.map_eq_zero_iff q.primeCompl (Localization.AtPrime q) _).mp hzero
  obtain ⟨s, hs⟩ := Ideal.Quotient.mk_surjective (t : MvPolynomial sigma F ⧸ J)
  have hs0 : aeval (fun _ : sigma => (0 : F)) s ≠ 0 := by
    have hden := t.property
    change zeroPointQuotientEvaluation J hJ (t : MvPolynomial sigma F ⧸ J) ≠ 0 at hden
    rw [← hs] at hden
    exact hden
  have hsp : s * projectiveDehomogenize P ∈ J := by
    apply Ideal.Quotient.eq_zero_iff_mem.mp
    rw [map_mul, hs]
    exact ht
  let S := projectiveHomogenize s s.totalDegree
  have hS : S.IsHomogeneous s.totalDegree := projectiveHomogenize_isHomogeneous _ _ le_rfl
  have hprod : projectiveDehomogenize (S * P) ∈ projectiveDehomogenizedIdeal I := by
    change projectiveDehomogenize (projectiveHomogenize s s.totalDegree * P) ∈ projectiveDehomogenizedIdeal I
    simpa only [map_mul, projectiveDehomogenize_homogenize] using hsp
  obtain ⟨k, hk⟩ := (homogeneous_dehomogenized_ideal_membership_iff I hI (S * P) (hS.mul hP)).mp hprod
  refine ⟨k + s.totalDegree, X none ^ k * S,
    (isHomogeneous_X_pow (R := F) (none : Option sigma) k).mul hS, ?_, ?_⟩
  · change aeval (fun j : Option sigma => j.elim 1 (fun _ => (0 : F)))
      (X none ^ k * projectiveHomogenize s s.totalDegree) ≠ 0
    simpa only [map_mul, map_pow, aeval_X, Option.elim_none, one_pow, one_mul,
      projectiveHomogenize_aeval_chart] using hs0
  · simpa only [mul_assoc] using hk

end DimensionFourDependence
