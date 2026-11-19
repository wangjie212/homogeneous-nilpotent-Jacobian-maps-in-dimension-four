import DimensionFourDependence.GenericAtlasLineObstructions

/-! # Lines through a hypersurface point lie in its tangent hyperplane

The first coefficient of the actual line restriction gives the tangent
equation for every vector in a contained line through the point. A nonzero
gradient makes its kernel a three-dimensional plane in four coordinates.
-/

namespace DimensionFourDependence

open MvPolynomial Matrix Module

variable {F : Type*} [Field F]

/-- The evaluated differential of the hypersurface equation at a point. -/
noncomputable def hypersurfaceTangentFunctional (R : MvPolynomial (Fin 4) F)
    (O : Fin 4 → F) : (Fin 4 → F) →ₗ[F] F where
  toFun D := ∑ i, aeval O (pderiv i R) * D i
  map_add' U V := by simp only [Pi.add_apply, mul_add, Finset.sum_add_distrib]
  map_smul' c U := by
    simp only [Pi.smul_apply, smul_eq_mul, Finset.mul_sum, RingHom.id_apply]
    apply Finset.sum_congr rfl
    intro i _
    ring

/-- The tangent hyperplane is the kernel of the evaluated differential. -/
noncomputable def hypersurfaceTangentPlane (R : MvPolynomial (Fin 4) F)
    (O : Fin 4 → F) : Submodule F (Fin 4 → F) := LinearMap.ker (hypersurfaceTangentFunctional R O)

/-- A contained projective line through the point lies in its actual tangent hyperplane. -/
theorem contained_line_le_hypersurfaceTangentPlane [Infinite F]
    (R : MvPolynomial (Fin 4) F) (O : Fin 4 → F) (L : Submodule F (Fin 4 → F))
    (hO : O ∈ L) (hL : ∀ x ∈ L, aeval x R = 0) : L ≤ hypersurfaceTangentPlane R O := by
  intro D hD
  have hline := contained_subspace_affine_line_identity R L hL O D hO hD
  have he := polynomial_line_linear_coefficient O D R
  rw [hline, Polynomial.coeff_zero] at he
  exact he.symm

/-- A nonzero gradient is a nonzero tangent functional. -/
theorem hypersurfaceTangentFunctional_ne_zero
    (R : MvPolynomial (Fin 4) F) (O : Fin 4 → F)
    (hsmooth : (fun i => aeval O (pderiv i R)) ≠ 0) : hypersurfaceTangentFunctional R O ≠ 0 := by
  intro hz
  apply hsmooth
  funext i
  have he := congrArg (fun f : (Fin 4 → F) →ₗ[F] F => f (Pi.single i 1)) hz
  simpa [hypersurfaceTangentFunctional, Pi.single_apply] using he

/-- At a smooth point the actual tangent kernel has vector dimension three. -/
theorem hypersurfaceTangentPlane_finrank
    (R : MvPolynomial (Fin 4) F) (O : Fin 4 → F)
    (hsmooth : (fun i => aeval O (pderiv i R)) ≠ 0) :
    finrank F (hypersurfaceTangentPlane R O) = 3 := by
  have he := Module.Dual.finrank_ker_add_one_of_ne_zero
    (hypersurfaceTangentFunctional_ne_zero R O hsmooth)
  simp only [Module.finrank_pi, Fintype.card_fin] at he
  change finrank F (LinearMap.ker (hypersurfaceTangentFunctional R O)) = 3
  omega

end DimensionFourDependence
