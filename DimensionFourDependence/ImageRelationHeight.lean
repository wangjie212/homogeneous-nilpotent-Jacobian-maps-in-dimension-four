import DimensionFourDependence.PolynomialCoefficientHeight

/-! # The rank-three image relation ideal has height at most one

Three independent outputs give injective polynomial coefficients. Regard
the fourth formal output as a single polynomial variable and apply the
coefficient-localization height bound. Reindexing variables preserves height.
-/

namespace DimensionFourDependence

open MvPolynomial

variable {K F σ τ : Type*} [Field K] [Field F] [Algebra K F]

/-- Reindexing a family by an equivalence preserves the height of its relation ideal. -/
theorem aeval_kernel_height_reindex (e : σ ≃ τ) (x : τ → F) :
    (RingHom.ker (aeval (x ∘ e) : MvPolynomial σ K →ₐ[K] F)).height =
      (RingHom.ker (aeval x : MvPolynomial τ K →ₐ[K] F)).height := by
  let E := renameEquiv K e
  have he : RingHom.ker (aeval (x ∘ e) : MvPolynomial σ K →ₐ[K] F) =
      (RingHom.ker (aeval x : MvPolynomial τ K →ₐ[K] F)).comap E.toRingHom := by
    ext p
    change aeval (x ∘ e) p = 0 ↔ aeval x (rename e p) = 0
    rw [aeval_rename]
  rw [he]
  exact E.toRingEquiv.height_comap _

/-- Adjoining one extra output to three independent ones gives a relation
ideal of height at most one, whether or not the extra output is algebraic. -/
theorem option_aeval_kernel_height_le_one (x : Fin 3 → F) (h : F)
    (hx : AlgebraicIndependent K x) :
    (RingHom.ker (aeval (fun j : Option (Fin 3) => j.elim h x) :
      MvPolynomial (Option (Fin 3)) K →ₐ[K] F)).height ≤ 1 := by
  let E := optionEquivLeft K (Fin 3)
  let f : Polynomial (MvPolynomial (Fin 3) K) →+* F :=
    Polynomial.eval₂RingHom (aeval x).toRingHom h
  let P := RingHom.ker f
  have : P.IsPrime := RingHom.ker_isPrime f
  have hcoeff : P.comap Polynomial.C = ⊥ := by
    ext p
    change f (Polynomial.C p) = 0 ↔ p = 0
    simpa [f] using (show aeval x p = 0 ↔ p = 0 from
      ⟨fun hp => hx (by simpa using hp), fun hp => by rw [hp, map_zero]⟩)
  have heval : f.comp E.toRingHom =
      (aeval (fun j : Option (Fin 3) => j.elim h x)).toRingHom := by
    apply MvPolynomial.ringHom_ext
    · intro a
      simp [f, E]
    · intro j
      cases j <;> simp [f, E]
  have hker : RingHom.ker (aeval (fun j : Option (Fin 3) => j.elim h x) :
        MvPolynomial (Option (Fin 3)) K →ₐ[K] F) = P.comap E.toRingHom := by
    ext p
    change aeval (fun j : Option (Fin 3) => j.elim h x) p = 0 ↔ f (E p) = 0
    have he := RingHom.congr_fun heval p
    change f (E p) = aeval (fun j : Option (Fin 3) => j.elim h x) p at he
    rw [he]
  calc
    _ = (P.comap E.toRingHom).height := congrArg Ideal.height hker
    _ = P.height := E.toRingEquiv.height_comap P
    _ ≤ 1 := polynomial_prime_height_le_one_of_coefficient_comap P hcoeff

/-- Three selected independent outputs bound the full relation ideal by height one. -/
theorem output_relation_prime_height_le_one (H : Fin 4 → F) (p : Equiv.Perm (Fin 4))
    (hY : AlgebraicIndependent K (fun i : Fin 3 => H (p i.castSucc))) :
    (fiberVanishingIdeal (L := K) H).height ≤ 1 := by
  let z : Option (Fin 3) → F := fun j => j.elim (H (p (Fin.last 3)))
    (fun i : Fin 3 => H (p i.castSucc))
  let e := finSuccEquiv' (Fin.last 3)
  have hpoint : z ∘ e = H ∘ p := by
    funext j
    refine Fin.lastCases ?_ (fun i => ?_) j
    · simp [z, e]
    · simp only [Function.comp_apply, e, finSuccEquiv'_below (Fin.castSucc_lt_last i), z,
        Option.elim_some]
  have he := aeval_kernel_height_reindex (K := K) e z
  rw [hpoint] at he
  change (RingHom.ker (aeval H : MvPolynomial (Fin 4) K →ₐ[K] F)).height ≤ 1
  calc
    _ = (RingHom.ker (aeval (H ∘ p) : MvPolynomial (Fin 4) K →ₐ[K] F)).height :=
      (aeval_kernel_height_reindex p H).symm
    _ = (RingHom.ker (aeval z : MvPolynomial (Option (Fin 3)) K →ₐ[K] F)).height := he
    _ ≤ 1 := option_aeval_kernel_height_le_one _ _ hY

end DimensionFourDependence
