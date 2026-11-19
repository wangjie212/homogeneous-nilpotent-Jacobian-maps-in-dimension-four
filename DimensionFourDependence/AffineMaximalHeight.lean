import DimensionFourDependence.Defs

/-! # Closed points in an affine domain have full transcendence height

The polynomial maximal-height calculation, Noether normalization and
going down over its normal polynomial base give the lower height bound
needed to distinguish surface divisors from closed points.
-/

namespace DimensionFourDependence

universe u

variable {k : Type u} [Field k]

/-- Every maximal ideal of a polynomial algebra in `n` variables over
a field has height exactly `n`. -/
theorem mvPolynomial_maximal_height (n : ℕ)
    (P : Ideal (MvPolynomial (Fin n) k)) [P.IsMaximal] : P.height = n := by
  induction n with
  | zero =>
    apply le_antisymm _ bot_le
    have h := Ideal.height_le_ringKrullDim_of_ne_top (I := P) Ideal.IsPrime.ne_top'
    have hdim : ringKrullDim (MvPolynomial (Fin 0) k) = 0 := by simp
    have h' : (P.height : WithBot ℕ∞) ≤ (0 : ℕ∞) := by simpa [hdim] using h
    exact WithBot.coe_le_coe.mp h'
  | succ n ih =>
    let e := MvPolynomial.finSuccEquiv k n
    let Q : Ideal (Polynomial (MvPolynomial (Fin n) k)) := P.map e.toRingHom
    letI : Q.IsMaximal := Ideal.map_isMaximal_of_equiv e.toRingEquiv
    let p : Ideal (MvPolynomial (Fin n) k) := Q.under (MvPolynomial (Fin n) k)
    letI : p.IsMaximal := Polynomial.isMaximal_comap_C_of_isJacobsonRing Q
    have he : Q.height = P.height := e.toRingEquiv.height_map P
    rw [← he, Polynomial.height_eq_height_add_one p Q, ih p]
    simp

variable {A : Type u} [CommRing A] [IsDomain A] [Algebra k A]
  [Algebra.FiniteType k A]

/-- In a finite-type domain with at least two independent parameters,
a maximal ideal has height at least two. The polynomial normalization
and its going-down action are constructed from the original algebra. -/
theorem two_le_height_of_isMaximal_finiteType
    (htr : 2 ≤ Algebra.trdeg k A) (Q : Ideal A) [Q.IsMaximal] :
    2 ≤ Q.height := by
  obtain ⟨n, g, hg, hint⟩ := exists_integral_inj_algHom_of_fg k A
  let S := MvPolynomial (Fin n) k
  letI : Algebra S A := g.toRingHom.toAlgebra
  letI : IsScalarTower k S A :=
    IsScalarTower.of_algebraMap_eq (fun c => (g.commutes c).symm)
  letI : FaithfulSMul S A := (faithfulSMul_iff_algebraMap_injective S A).mpr hg
  letI : Algebra.IsIntegral S A := ⟨hint⟩
  have hdim : (n : Cardinal) = Algebra.trdeg k A := by
    have h := trdeg_add_eq (A := A) k S
    simpa [trdeg_eq_zero, S, MvPolynomial.trdeg_of_isDomain] using h
  have hn : 2 ≤ n := by
    have h : (2 : Cardinal) ≤ n := by rwa [hdim]
    exact_mod_cast h
  let p : Ideal S := Q.under S
  letI : p.IsMaximal := Ideal.isMaximal_under_of_isIntegral_of_isMaximal Q
  letI : IsNoetherianRing A := Algebra.FiniteType.isNoetherianRing k A
  have hp : p.height = n := mvPolynomial_maximal_height n p
  have hheight := Ideal.height_eq_height_add_of_liesOver_of_hasGoingDown p Q
  have hle : p.height ≤ Q.height := by rw [hheight]; exact le_self_add
  exact (show (2 : ℕ∞) ≤ n by exact_mod_cast hn).trans (hp ▸ hle)

/-- A height-one prime in an affine domain of transcendence degree at
least two is not a closed point. -/
theorem height_one_prime_not_isMaximal_finiteType
    (htr : 2 ≤ Algebra.trdeg k A) (Q : Ideal A) [Q.IsPrime]
    (hQ : Q.height = 1) : ¬ Q.IsMaximal := by
  intro hm
  letI : Q.IsMaximal := hm
  have h := two_le_height_of_isMaximal_finiteType (k := k) htr Q
  rw [hQ] at h
  exact (by decide : ¬ (2 : ℕ∞) ≤ 1) h

end DimensionFourDependence
