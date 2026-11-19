import DimensionFourDependence.ProjectivePointEquationRegularity
import Mathlib.RingTheory.UniqueFactorizationDomain.Multiplicity

/-! # Exact homogeneous cofactors along the direction equation

Removing the full multiplicity of the actual irreducible direction
equation leaves an original homogeneous polynomial with nonzero value
at the generic direction. Its degree and the multiplicity are derived
from the original polynomial, as required by Section 4.5.
-/

namespace DimensionFourDependence

open MvPolynomial

attribute [local instance] MvPolynomial.gradedAlgebra

variable {K F σ : Type*} [Field K] [Field F] [Algebra K F]

/-- The full actual factor multiplicity supplies a homogeneous
cofactor nonvanishing at the generic direction, with the exact degree. -/
theorem direction_equation_multiplicity_cofactor
    (A : σ → F) (Φ : MvPolynomial σ K) {δ : ℕ}
    (hΦ : Φ.IsHomogeneous δ) (hirr : Irreducible Φ)
    (hI : (projectiveFieldPointIdeal (E := K) A).toIdeal = Ideal.span {Φ})
    (P : MvPolynomial σ K) {e : ℕ} (hP0 : P ≠ 0) (hP : P.IsHomogeneous e) :
    ∃ R : MvPolynomial σ K,
      P = Φ ^ multiplicity Φ P * R ∧ R ≠ 0 ∧ ¬ Φ ∣ R ∧
      R.IsHomogeneous (e - δ * multiplicity Φ P) ∧
      aeval A R ≠ 0 ∧ δ * multiplicity Φ P ≤ e ∧ multiplicity Φ P ≤ e := by
  have hfin : FiniteMultiplicity Φ P := .of_not_isUnit hirr.not_isUnit hP0
  obtain ⟨R, hR, hnot⟩ := hfin.exists_eq_pow_mul_and_not_dvd
  have hmul : Φ ^ multiplicity Φ P * R ≠ 0 := by rwa [← hR]
  have hR0 : R ≠ 0 := right_ne_zero_of_mul hmul
  obtain ⟨f, hf⟩ := isHomogeneous_of_mul_left
    (p := R) (q := Φ ^ multiplicity Φ P)
    (by rw [mul_comm]; exact hR ▸ hP) (by rwa [mul_comm])
  have hdegree : δ * multiplicity Φ P + f = e :=
    ((hΦ.pow (multiplicity Φ P)).mul hf).inj_right (hR ▸ hP) hmul
  have hf' : f = e - δ * multiplicity Φ P := by omega
  have hval : aeval A R ≠ 0 := by
    intro hz
    exact hnot ((principal_projective_equation_vanishing_iff_dvd A Φ hI R hf).mp hz)
  have hδ : 0 < δ :=
    (principal_projective_equation_irreducible_degree_pos A Φ hirr.ne_zero hΦ hI).2
  refine ⟨R, hR, hR0, hnot, hf' ▸ hf, hval, by omega, ?_⟩
  exact (Nat.le_mul_of_pos_left (multiplicity Φ P) hδ).trans (by omega)

end DimensionFourDependence
