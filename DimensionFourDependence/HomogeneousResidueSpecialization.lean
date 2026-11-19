import DimensionFourDependence.CurvePoleValuation

/-! # Homogeneous equations specialize under normalized residue coordinates

A valuation-normalized homogeneous point has integral coordinates. Its
equations reduce to equations of the residue point, including equations
of the actual projective closure and leading equations at infinity.
-/

namespace DimensionFourDependence

open MvPolynomial

variable {E A σ : Type*} [Field E] [CommRing A] [Algebra E A]

/-- Homogeneous scaling for arbitrary variable indices, including the
`Option` indices of the project's homogeneous coordinates. -/
theorem homogeneous_aeval_scale_indexed (P : MvPolynomial σ E) {d : ℕ}
    (hP : P.IsHomogeneous d) (x : σ → A) (r : A) :
    aeval (fun i => r * x i) P = r ^ d * aeval x P := by
  let e : Polynomial (MvPolynomial σ E) →ₐ[E] A :=
    ((Polynomial.aeval r).restrictScalars E).comp (Polynomial.mapAlgHom (aeval x))
  have hC (Q : MvPolynomial σ E) : e (Polynomial.C Q) = aeval x Q := by
    change Polynomial.aeval r (Polynomial.map (aeval x).toRingHom (Polynomial.C Q)) = _
    rw [Polynomial.map_C, Polynomial.aeval_C]
    rfl
  have hX : e Polynomial.X = r := by
    change Polynomial.aeval r (Polynomial.map (aeval x).toRingHom Polynomial.X) = r
    rw [Polynomial.map_X, Polynomial.aeval_X]
  have he : e.comp gradeHom = aeval (fun i => r * x i) := by
    apply MvPolynomial.algHom_ext
    intro i
    simp only [AlgHom.comp_apply, aeval_X]
    change e (gradeHom (X i)) = r * x i
    have hg : gradeHom (X i : MvPolynomial σ E) = Polynomial.C (X i) * Polynomial.X := by
      simp only [gradeHom, aeval_X]
    rw [hg, map_mul, hC, hX, aeval_X]
    exact mul_comm _ _
  rw [← DFunLike.congr_fun he P, AlgHom.comp_apply, gradeHom_of_isHomogeneous hP]
  rw [← Polynomial.C_mul_X_pow_eq_monomial, map_mul, map_pow, hC, hX]
  exact mul_comm _ _

variable {O F κ : Type*} [CommRing O] [Field F] [CommRing κ]
    [Algebra E O] [Algebra E F] [Algebra O F] [IsScalarTower E O F] [Algebra E κ]

/-- Every homogeneous equation of a point survives reduction of any
integral common rescaling of its coordinates. -/
theorem homogeneous_residue_specialization
    (π : O →ₐ[E] κ) (hinj : Function.Injective (algebraMap O F))
    (x : σ → F) (s : F) (z : σ → O)
    (hz : ∀ i, algebraMap O F (z i) = s * x i)
    (P : MvPolynomial σ E) {d : ℕ} (hP : P.IsHomogeneous d) (hzero : aeval x P = 0) :
    aeval (fun i => π (z i)) P = 0 := by
  have he := comp_aeval_apply z (IsScalarTower.toAlgHom E O F) P
  change algebraMap O F (aeval z P) = aeval (fun i => algebraMap O F (z i)) P at he
  rw [funext hz, homogeneous_aeval_scale_indexed P hP x s, hzero, mul_zero] at he
  have ho : aeval z P = 0 := hinj (by simpa only [map_zero] using he)
  have hk := comp_aeval_apply z π P
  rw [ho, map_zero] at hk
  exact hk.symm

/-- Affine equations reduce through actual-degree homogenization at
every normalized point, including its infinity boundary. -/
theorem homogenized_equation_residue_specialization
    (π : O →ₐ[E] κ) (hinj : Function.Injective (algebraMap O F))
    (x : σ → F) (s : F) (z : Option σ → O)
    (hz0 : algebraMap O F (z none) = s)
    (hz : ∀ i, algebraMap O F (z (some i)) = s * x i)
    (P : MvPolynomial σ E) (d : ℕ) (hd : P.totalDegree ≤ d) (hzero : aeval x P = 0) :
    aeval (fun i => π (z i)) (projectiveHomogenize P d) = 0 := by
  apply homogeneous_residue_specialization π hinj (fun j : Option σ => j.elim 1 x) s z
    (fun j => by cases j <;> simp only [Option.elim_none, Option.elim_some, mul_one, hz0, hz])
    (projectiveHomogenize P d) (projectiveHomogenize_isHomogeneous P d hd)
  rw [projectiveHomogenize_aeval_chart, hzero]

end DimensionFourDependence
