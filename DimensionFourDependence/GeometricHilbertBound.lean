import DimensionFourDependence.HilbertFieldExtension

/-! # Hilbert degree bounds after extending the coefficient field

The entire closure keeps its Hilbert polynomial under every field extension.
Every subcurve of that extended closure has no larger Hilbert degree. This
does not yet identify the paper's geometric generic components with subcurves.
-/

namespace DimensionFourDependence

open MvPolynomial

variable {L : Type*} [Field L] (E : Type*) [Field E] [Algebra L E] {σ : Type*}

attribute [local instance] MvPolynomial.gradedAlgebra

/-- Extending the coefficient field preserves homogeneity of the relation ideal. -/
theorem extendCoefficientIdeal_isHomogeneous (I : Ideal (MvPolynomial σ L))
    (hI : I.IsHomogeneous (homogeneousSubmodule σ L)) :
    (extendCoefficientIdeal E I).IsHomogeneous (homogeneousSubmodule σ E) := by
  obtain ⟨S, hS⟩ := (Ideal.IsHomogeneous.iff_exists (𝒜 := homogeneousSubmodule σ L) (I := I)).mp hI
  unfold extendCoefficientIdeal
  rw [hS, Ideal.map_span]
  apply Ideal.homogeneous_span
  rintro _ ⟨p, ⟨s, hs, rfl⟩, rfl⟩
  obtain ⟨d, hd⟩ := s.property
  exact ⟨d, (show (s : MvPolynomial σ L).IsHomogeneous d from hd).map (algebraMap L E)⟩

/-- The actual Hilbert polynomial is unchanged under an arbitrary field extension. -/
theorem projectiveHilbertPolynomial_field_extension [Finite σ]
    (I : Ideal (MvPolynomial σ L)) (hI : I.IsHomogeneous (homogeneousSubmodule σ L)) :
    projectiveHilbertPolynomial (extendCoefficientIdeal E I) (extendCoefficientIdeal_isHomogeneous E I hI) =
      projectiveHilbertPolynomial I hI := by
  obtain ⟨N, hN⟩ := projectiveHilbertPolynomial_spec I hI
  apply Eq.symm
  apply projectiveHilbertPolynomial_unique _ _ _ N
  intro n hn
  rw [projectiveHilbertFunction_field_extension]
  exact hN n hn

/-- Comparing eventual integral linear functions compares their slopes. -/
theorem integer_linear_slope_le (a b c d : ℤ) (N : ℕ)
    (h : ∀ n ≥ N, a * (n : ℤ) + b ≤ c * (n : ℤ) + d) : a ≤ c := by
  by_contra hac
  have hcoeff : c + 1 ≤ a := by omega
  let n := N + (d - b).natAbs + 1
  have hn : N ≤ n := by dsimp only [n]; omega
  have hlarge : ((d - b).natAbs : ℤ) + 1 ≤ (n : ℤ) := by
    dsimp only [n]
    push_cast
    omega
  have habs : d - b ≤ ((d - b).natAbs : ℤ) := Int.le_natAbs
  have hprod := mul_le_mul_of_nonneg_right hcoeff (show (0 : ℤ) ≤ n by positivity)
  have hbound := h n hn
  nlinarith

/-- A projective subcurve has no larger Hilbert degree than the curve containing it. -/
theorem curveHilbertDegree_le_of_ideal_le [Finite σ]
    {I J : Ideal (MvPolynomial σ L)} (hIJ : I ≤ J) {e e' : ℕ}
    (he : HasCurveHilbertDegree I e) (he' : HasCurveHilbertDegree J e') : e' ≤ e := by
  obtain ⟨_, b, N, hN⟩ := he
  obtain ⟨_, b', M, hM⟩ := he'
  have hsl := integer_linear_slope_le (e' : ℤ) b' (e : ℤ) b (max N M) (by
    intro n hn
    have hdim : (projectiveHilbertFunction J n : ℤ) ≤ projectiveHilbertFunction I n := by
      exact_mod_cast projectiveHilbertFunction_antitone hIJ n
    rw [hN n (by omega), hM n (by omega)] at hdim
    exact hdim)
  exact_mod_cast hsl

variable {K : Type*} [Field K] [CharZero K]

/-- The actual generic fiber's positive degree at most six is preserved
after every extension of its coefficient field, including an algebraic closure. -/
theorem projective_fiber_witness_field_extension_degree
    (H : Fin 4 → FractionRing (MvPolynomial (Fin 4) K))
    (hN : IsNilpotent (rationalJacobian H)) (hrank : (rationalJacobian H).rank = 3)
    (W : ProjectiveFiberEquationWitness H) (Fext : Type*) [Field Fext]
    [Algebra (coefficientField (K := K) (fun i : Fin 3 => H (W.affine.chart i.castSucc))) Fext] :
    ∃ e : ℕ, e ≤ 6 ∧ HasCurveHilbertDegree (extendCoefficientIdeal Fext (projectiveConeIdeal
      (L := coefficientField (K := K) (fun i : Fin 3 => H (W.affine.chart i.castSucc)))
      (fun i : Fin 3 => rationalCoordinate (K := K) (W.affine.chart i.castSucc)))) e := by
  obtain ⟨e, he6, he⟩ := projective_fiber_witness_curve_hilbert_degree H hN hrank W
  exact ⟨e, he6, curveHilbertDegree_field_extension Fext _ e he⟩

/-- Every projective subcurve of the scalar-extended fiber closure has degree at most six. -/
theorem projective_fiber_witness_extended_subcurve_degree_le_six
    (H : Fin 4 → FractionRing (MvPolynomial (Fin 4) K))
    (hN : IsNilpotent (rationalJacobian H)) (hrank : (rationalJacobian H).rank = 3)
    (W : ProjectiveFiberEquationWitness H) (Fext : Type*) [Field Fext]
    [Algebra (coefficientField (K := K) (fun i : Fin 3 => H (W.affine.chart i.castSucc))) Fext]
    (J : Ideal (MvPolynomial (Option (Fin 3)) Fext))
    (hJ : extendCoefficientIdeal Fext (projectiveConeIdeal
      (L := coefficientField (K := K) (fun i : Fin 3 => H (W.affine.chart i.castSucc)))
      (fun i : Fin 3 => rationalCoordinate (K := K) (W.affine.chart i.castSucc))) ≤ J)
    (e : ℕ) (he : HasCurveHilbertDegree J e) : e ≤ 6 := by
  obtain ⟨d, hd6, hd⟩ := projective_fiber_witness_field_extension_degree H hN hrank W Fext
  exact (curveHilbertDegree_le_of_ideal_le hJ hd he).trans hd6

end DimensionFourDependence
