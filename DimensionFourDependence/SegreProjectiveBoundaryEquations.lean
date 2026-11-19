import DimensionFourDependence.SegreGraphDifferentials
import DimensionFourDependence.ProjectiveModifiedBoundaryEquation

/-! # Original Segre fiber equations at actual points at infinity -/

namespace DimensionFourDependence

open MvPolynomial Matrix

set_option maxHeartbeats 3000000

variable {K E κ : Type*} [Field K] [Field E] [Algebra K E] [Field κ] [Algebra E κ]
    (δ : Fin 3 → Derivation K E E) (Y : Fin 3 → E)
    (hcoord : ∀ i j, δ i (Y j) = if j = i then 1 else 0) (hY0 : Y 0 ≠ 0)

include hcoord hY0

/-- The Segre quadratic graph expression remains the same product
after any coefficient extension and on arbitrary residue direction coordinates. -/
theorem segre_graph_half_hessian_pairing_base_change [CharZero E]
    (b : Fin 3 → κ) :
    (2 : κ)⁻¹ * matrixBilinearPairing ((derivationHessian δ (segreGraphFunction Y)).map (algebraMap E κ)) b b =
      (b 1 - algebraMap E κ (Y 1) / algebraMap E κ (Y 0) * b 0) *
        (b 2 - algebraMap E κ (Y 2) / algebraMap E κ (Y 0) * b 0) / algebraMap E κ (Y 0) := by
  letI : CharZero κ := charZero_of_injective_algebraMap (algebraMap E κ).injective
  have hr : algebraMap E κ (Y 0) ≠ 0 := (map_ne_zero (algebraMap E κ)).mpr hY0
  rw [segre_graph_hessian δ Y hcoord hY0]
  simp [matrixBilinearPairing, Matrix.map_apply, Fin.sum_univ_succ, map_div₀, map_pow, map_ofNat]
  field_simp
  ring

omit hY0 in
/-- Multiplication by the original radial output gives exactly the
two gradient cross terms required in the boundary equation for `rc`. -/
theorem segre_radial_product_hessian_pairing_base_change (c : E) (b : Fin 3 → κ) :
    matrixBilinearPairing ((derivationHessian δ (Y 0 * c)).map (algebraMap E κ)) b b =
      algebraMap E κ (Y 0) * matrixBilinearPairing ((derivationHessian δ c).map (algebraMap E κ)) b b +
        2 * b 0 * ∑ i, algebraMap E κ (δ i c) * b i := by
  simp [matrixBilinearPairing, derivationHessian, Matrix.map_apply, Fin.sum_univ_succ,
    Derivation.leibniz, smul_eq_mul, hcoord]
  ring

variable [CharZero E]
variable {F σ : Type*} [Field F] [Algebra E F]

/-- The original quadratic and cubic equations imply both ruling
membership and `D²(rc)[b,b]=0` at every actual projective boundary point.
The reduced quadratic equation and its Hessian are derived internally. -/
theorem segre_graph_projective_boundary_equations
    (x : σ → F) (z : Option σ → κ) (hz : z ≠ 0)
    (hpoint : projectiveFieldPoint (E := E) z hz ∈ projectiveClosureSet (L := E) x)
    (hz0 : z none = 0) (f : Fin 3 → σ) (c q k : E)
    (hQ : aeval (x ∘ f) (quadraticFiberPolynomial (fun i => δ i c)
      (derivationHessian δ (segreGraphFunction Y)) q) = 0)
    (hC : aeval (x ∘ f) (cubicFiberPolynomial (fun i => δ i q)
      (derivationHessian δ c) (derivationCubicTensor δ (segreGraphFunction Y)) k) = 0) :
    ((z (some (f 1)) - algebraMap E κ (Y 1) / algebraMap E κ (Y 0) * z (some (f 0))) *
      (z (some (f 2)) - algebraMap E κ (Y 2) / algebraMap E κ (Y 0) * z (some (f 0))) = 0) ∧
      matrixBilinearPairing ((derivationHessian δ (Y 0 * c)).map (algebraMap E κ))
        (fun i => z (some (f i))) (fun i => z (some (f i))) = 0 := by
  letI : CharZero κ := charZero_of_injective_algebraMap (algebraMap E κ).injective
  have hr : algebraMap E κ (Y 0) ≠ 0 := (map_ne_zero (algebraMap E κ)).mpr hY0
  let b : Fin 3 → κ := fun i => z (some (f i))
  have hiso := projective_fiber_closure_quadratic_isotropic x z hz hpoint hz0 f
    (fun i => δ i c) (derivationHessian δ (segreGraphFunction Y)) q hQ
  have he := segre_graph_half_hessian_pairing_base_change δ Y hcoord hY0 b
  have hprod : (b 1 - algebraMap E κ (Y 1) / algebraMap E κ (Y 0) * b 0) *
      (b 2 - algebraMap E κ (Y 2) / algebraMap E κ (Y 0) * b 0) = 0 := by
    rw [hiso, mul_zero] at he
    have hzdiv := he.symm
    simpa only [div_eq_zero_iff, hr, or_false] using hzdiv
  refine ⟨hprod, ?_⟩
  have hfactor : cubicFormPolynomial (derivationCubicTensor δ (segreGraphFunction Y)) =
      linearFormPolynomial (![-3 / Y 0, 0, 0] : Fin 3 → E) *
        quadraticFormPolynomial (derivationHessian δ (segreGraphFunction Y)) :=
    cubicFormPolynomial_eq_linear_mul_quadratic_of_polarization _ _ _
      (segre_graph_cubic_polarization δ Y hcoord hY0)
  have hm := projective_closure_modified_cubic_boundary_equation x z hz hpoint hz0 f
    (fun i => δ i c) (fun i => δ i q) (![-3 / Y 0, 0, 0] : Fin 3 → E)
    (derivationHessian δ (segreGraphFunction Y)) (derivationHessian δ c)
    (derivationCubicTensor δ (segreGraphFunction Y)) q k hfactor hQ hC
  change matrixBilinearPairing ((derivationHessian δ c).map (algebraMap E κ)) b b -
    (2 / 3 : κ) * ((fun i => algebraMap E κ ((![-3 / Y 0, 0, 0] : Fin 3 → E) i)) ⬝ᵥ b) *
      ((fun i => algebraMap E κ (δ i c)) ⬝ᵥ b) = 0 at hm
  have hΛ : ((fun i => algebraMap E κ ((![-3 / Y 0, 0, 0] : Fin 3 → E) i)) ⬝ᵥ b) =
      (-3 / algebraMap E κ (Y 0)) * b 0 := by
    simp [dotProduct, Fin.sum_univ_succ, map_div₀, map_ofNat]
  rw [hΛ] at hm
  change matrixBilinearPairing ((derivationHessian δ (Y 0 * c)).map (algebraMap E κ)) b b = 0
  rw [segre_radial_product_hessian_pairing_base_change δ Y hcoord c b]
  field_simp [hr] at hm
  simp only [dotProduct] at hm
  linear_combination hm

end DimensionFourDependence
