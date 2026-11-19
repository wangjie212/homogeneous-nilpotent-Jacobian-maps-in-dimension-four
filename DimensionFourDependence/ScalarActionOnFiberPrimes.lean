import DimensionFourDependence.AffineSubstitutionDegree
import Mathlib.RingTheory.Ideal.MinimalPrime.Localization
import Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed
import Mathlib.GroupTheory.GroupAction.Quotient

/-! # Scalar multiplication as an action on geometric fiber components -/

namespace DimensionFourDependence

open MvPolynomial

universe u
set_option maxHeartbeats 3400000

variable {E : Type u} [Field E] {n : ℕ}
local notation "R₀" => MvPolynomial (Fin n) E

/-- Polynomial pullback of multiplication of every source coordinate by
one nonzero scalar, with its actual inverse substitution. -/
noncomputable def polynomialScalarEquiv (u : Eˣ) : R₀ ≃ₐ[E] R₀ := by
  let f : R₀ →ₐ[E] R₀ := aeval (fun i => C (u : E) * X i)
  let g : R₀ →ₐ[E] R₀ := aeval (fun i => C ((u⁻¹ : Eˣ) : E) * X i)
  apply AlgEquiv.ofAlgHom f g
  · apply MvPolynomial.algHom_ext
    intro i
    simp only [f, g, AlgHom.comp_apply, AlgHom.id_apply, aeval_X]
    rw [map_mul, aeval_C, algebraMap_eq, aeval_X, ← mul_assoc, ← map_mul,
      Units.inv_mul, map_one, one_mul]
  · apply MvPolynomial.algHom_ext
    intro i
    simp only [f, g, AlgHom.comp_apply, AlgHom.id_apply, aeval_X]
    rw [map_mul, aeval_C, algebraMap_eq, aeval_X, ← mul_assoc, ← map_mul,
      Units.mul_inv, map_one, one_mul]

theorem polynomialScalarEquiv_apply (u : Eˣ) (p : R₀) :
    polynomialScalarEquiv u p = aeval (fun i => C (u : E) * X i) p := rfl

theorem polynomialScalarEquiv_one : polynomialScalarEquiv (n := n) (1 : Eˣ) = AlgEquiv.refl := by
  have h : (polynomialScalarEquiv (n := n) (1 : Eˣ)).toAlgHom = AlgHom.id E R₀ := by
    apply MvPolynomial.algHom_ext
    intro i
    change polynomialScalarEquiv (1 : Eˣ) (X i) = X i
    rw [polynomialScalarEquiv_apply, aeval_X]
    simp
  apply AlgEquiv.ext
  intro p
  exact DFunLike.congr_fun h p

theorem polynomialScalarEquiv_mul (u v : Eˣ) :
    (polynomialScalarEquiv (n := n) (u * v)).toRingHom =
      (polynomialScalarEquiv u).toRingHom.comp (polynomialScalarEquiv v).toRingHom := by
  have h : (polynomialScalarEquiv (n := n) (u * v)).toAlgHom =
      (polynomialScalarEquiv u).toAlgHom.comp (polynomialScalarEquiv v).toAlgHom := by
    apply MvPolynomial.algHom_ext
    intro i
    change polynomialScalarEquiv (u * v) (X i) = polynomialScalarEquiv u (polynomialScalarEquiv v (X i))
    rw [polynomialScalarEquiv_apply, aeval_X, polynomialScalarEquiv_apply v, aeval_X,
      map_mul, show (polynomialScalarEquiv u) (C (v : E)) = C (v : E) from (polynomialScalarEquiv u).commutes _,
      polynomialScalarEquiv_apply, aeval_X, Units.val_mul, map_mul]
    ring
  exact congrArg AlgHom.toRingHom h

/-- When every scalar pullback preserves an ideal, scalar multiplication
acts on its minimal primes by inverse image, the action on component
points induced by multiplication of the original coordinates. -/
@[instance_reducible] noncomputable def scalarActionOnMinimalPrimes (d : ℕ) (J : Ideal R₀)
    (hJ : ∀ u : rootsOfUnity d E, J.comap (polynomialScalarEquiv (u : Eˣ)).toRingHom = J) :
    MulAction (rootsOfUnity d E) J.minimalPrimes where
  smul u P := ⟨P.val.comap (polynomialScalarEquiv (u : Eˣ)).toRingHom, by
    have h := Ideal.minimalPrimes_comap_of_surjective (f := (polynomialScalarEquiv (u : Eˣ)).toRingHom)
      (polynomialScalarEquiv (u : Eˣ)).surjective P.property
    rwa [hJ u] at h⟩
  one_smul P := by
    apply Subtype.val_injective
    change P.val.comap (polynomialScalarEquiv (1 : Eˣ)).toRingHom = P.val
    rw [polynomialScalarEquiv_one]
    exact Ideal.comap_id _
  mul_smul u v P := by
    apply Subtype.val_injective
    change P.val.comap (polynomialScalarEquiv ((u : Eˣ) * (v : Eˣ))).toRingHom =
      (P.val.comap (polynomialScalarEquiv (v : Eˣ)).toRingHom).comap (polynomialScalarEquiv (u : Eˣ)).toRingHom
    rw [mul_comm (u : Eˣ), polynomialScalarEquiv_mul, Ideal.comap_comap]

/-- A component on which one coordinate has a nonzero constant value
has trivial stabilizer under scalar multiplication. -/
theorem scalar_stabilizer_trivial_of_nonzero_coordinate_value
    (P : Ideal R₀) [P.IsPrime] (i : Fin n) (a : E) (ha : a ≠ 0)
    (hval : X i - C a ∈ P) (u : Eˣ)
    (hfix : P.comap (polynomialScalarEquiv u).toRingHom = P) : u = 1 := by
  have hmem : polynomialScalarEquiv u (X i - C a) ∈ P := by
    change X i - C a ∈ P.comap (polynomialScalarEquiv u).toRingHom
    rwa [hfix]
  rw [map_sub, polynomialScalarEquiv_apply u (X i), aeval_X,
    show (polynomialScalarEquiv u) (C a) = C a from (polynomialScalarEquiv u).commutes a] at hmem
  have hnew : C (((u : E) - 1) * a) ∈ P := by
    have hg := P.sub_mem hmem (P.mul_mem_left (C (u : E)) hval)
    have he : C (u : E) * X i - C a - C (u : E) * (X i - C a) = C (((u : E) - 1) * a) := by
      simp only [map_mul, map_sub, map_one]
      ring
    rwa [he] at hg
  apply Units.ext
  apply sub_eq_zero.mp
  by_contra hz
  have hu : IsUnit (C (((u : E) - 1) * a) : R₀) :=
    (isUnit_iff_ne_zero.mpr (mul_ne_zero hz ha)).map C
  exact (Ideal.IsPrime.ne_top inferInstance) (Ideal.eq_top_of_isUnit_mem P hnew hu)

end DimensionFourDependence
