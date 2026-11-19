import DimensionFourDependence.FiberPrimeHeight
import DimensionFourDependence.ProjectiveFiberEquations

/-! # The homogeneous prime of the projective closure

The cone is parametrized by `t · (1,x)`. Its ideal is a kernel into the
domain `F[t]`, so its primality does not require an algebraically closed base.
-/

namespace DimensionFourDependence

open MvPolynomial

variable {L F σ : Type*} [Field L] [Field F] [Algebra L F]

/-- The graded evaluation map at the generic line through `(1,x)`. -/
noncomputable def projectiveConeMap (x : σ → F) :
    MvPolynomial (Option σ) L →ₐ[L] Polynomial F :=
  (Polynomial.mapAlgHom (aeval (fun j : Option σ => j.elim 1 x))).comp gradeHom

/-- The homogeneous relation ideal of the projective closure of the point. -/
noncomputable def projectiveConeIdeal (x : σ → F) : Ideal (MvPolynomial (Option σ) L) :=
  RingHom.ker (projectiveConeMap (L := L) x)

@[instance]
theorem projectiveConeIdeal_isPrime (x : σ → F) : (projectiveConeIdeal (L := L) x).IsPrime :=
  RingHom.ker_isPrime (projectiveConeMap (L := L) x)

theorem projectiveConeMap_X (x : σ → F) (j : Option σ) :
    projectiveConeMap (L := L) x (X j) = Polynomial.C (j.elim 1 x) * Polynomial.X := by
  simp [projectiveConeMap, gradeHom]

/-- Each coefficient is the value of the corresponding homogeneous component. -/
theorem projectiveConeMap_coeff (x : σ → F) (p : MvPolynomial (Option σ) L) (d : ℕ) :
    (projectiveConeMap (L := L) x p).coeff d =
      aeval (fun j : Option σ => j.elim 1 x) (homogeneousComponent d p) := by
  simp [projectiveConeMap, coeff_gradeHom]

theorem projectiveConeMap_of_isHomogeneous (x : σ → F)
    {p : MvPolynomial (Option σ) L} {d : ℕ} (hp : p.IsHomogeneous d) :
    projectiveConeMap (L := L) x p =
      Polynomial.monomial d (aeval (fun j : Option σ => j.elim 1 x) p) := by
  simp [projectiveConeMap, gradeHom_of_isHomogeneous hp]

/-- A homogeneous equation belongs to the closure prime exactly when it
vanishes at the actual projective generic point. -/
theorem projectiveConeIdeal_mem_of_isHomogeneous (x : σ → F)
    {p : MvPolynomial (Option σ) L} {d : ℕ} (hp : p.IsHomogeneous d) :
    p ∈ projectiveConeIdeal (L := L) x ↔ aeval (fun j : Option σ => j.elim 1 x) p = 0 := by
  change projectiveConeMap (L := L) x p = 0 ↔ _
  rw [projectiveConeMap_of_isHomogeneous x hp, Polynomial.monomial_eq_zero_iff]

/-- The cone relation ideal is closed under taking homogeneous components. -/
theorem projectiveConeIdeal_homogeneousComponent_mem (x : σ → F)
    {p : MvPolynomial (Option σ) L} (hp : p ∈ projectiveConeIdeal (L := L) x) (d : ℕ) :
    homogeneousComponent d p ∈ projectiveConeIdeal (L := L) x := by
  apply (projectiveConeIdeal_mem_of_isHomogeneous x (homogeneousComponent_isHomogeneous d p)).mpr
  rw [← projectiveConeMap_coeff]
  change projectiveConeMap (L := L) x p = 0 at hp
  rw [hp, Polynomial.coeff_zero]

theorem projectiveConeMap_eval_one (x : σ → F) (p : MvPolynomial (Option σ) L) :
    (projectiveConeMap (L := L) x p).eval 1 = aeval (fun j : Option σ => j.elim 1 x) p := by
  have he : ((Polynomial.aeval (1 : F)).restrictScalars L).comp (projectiveConeMap (L := L) x) =
      aeval (fun j : Option σ => j.elim 1 x) := by
    apply MvPolynomial.algHom_ext
    intro j
    simp [projectiveConeMap_X]
  exact DFunLike.congr_fun he p

/-- The homogenizing coordinate does not vanish on the closure. -/
theorem projectiveConeIdeal_X_none_not_mem (x : σ → F) :
    X none ∉ projectiveConeIdeal (L := L) x := by
  change projectiveConeMap (L := L) x (X none) ≠ 0
  simp [projectiveConeMap_X]

/-- The affine chart ideal strictly contains the cone ideal; `X₀-1`
witnesses the strict inclusion. -/
theorem projectiveConeIdeal_lt_chart (x : σ → F) :
    projectiveConeIdeal (L := L) x <
      RingHom.ker (aeval (fun j : Option σ => j.elim 1 x) : MvPolynomial (Option σ) L →ₐ[L] F) := by
  apply lt_of_le_of_ne
  · intro p hp
    change aeval (fun j : Option σ => j.elim 1 x) p = 0
    rw [← projectiveConeMap_eval_one]
    change projectiveConeMap (L := L) x p = 0 at hp
    rw [hp, Polynomial.eval_zero]
  · intro he
    have hm : X none - 1 ∈ RingHom.ker
        (aeval (fun j : Option σ => j.elim 1 x) : MvPolynomial (Option σ) L →ₐ[L] F) := by
      simp
    rw [← he] at hm
    change projectiveConeMap (L := L) x (X none - 1) = 0 at hm
    have hc := congrArg (fun p : Polynomial F => p.coeff 0) hm
    simp [map_sub, projectiveConeMap_X] at hc

end DimensionFourDependence
