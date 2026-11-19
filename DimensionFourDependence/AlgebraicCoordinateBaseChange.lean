import DimensionFourDependence.Defs

/-! # Dimension and original coordinate equations under algebraic base change

When the extended chart is a domain, an algebraic coefficient extension
preserves its transcendence degree. Original algebra generators remain
generators, nonzero original coordinates remain nonzero, and the extended
original equation still vanishes at those exact coordinate elements.
-/

namespace DimensionFourDependence

universe u

open scoped TensorProduct

variable {k E A : Type u} [Field k] [Field E] [Algebra k E]
  [CommRing A] [IsDomain A] [Algebra k A]

/-- Algebraic extension of coefficients preserves the transcendence
degree of a geometrically integral affine chart. -/
theorem algebraic_tensor_base_change_trdeg
    [Algebra.IsAlgebraic k E] [IsDomain (E ⊗[k] A)] :
    Algebra.trdeg E (E ⊗[k] A) = Algebra.trdeg k A := by
  let T := A ⊗[k] E
  let : IsDomain T := Function.Injective.isDomain
    (Algebra.TensorProduct.comm k A E) (Algebra.TensorProduct.comm k A E).injective
  let : FaithfulSMul A T := (faithfulSMul_iff_algebraMap_injective A T).mpr
    (Algebra.TensorProduct.includeLeft_injective (R := k) (S := A) (A := A) (B := E)
      (algebraMap k E).injective)
  have hA := trdeg_add_eq (A := T) k A
  have hzA : Algebra.trdeg A T = 0 := trdeg_eq_zero
  rw [hzA, add_zero] at hA
  have hE := trdeg_add_eq (A := E ⊗[k] A) k E
  have hzE : Algebra.trdeg k E = 0 := trdeg_eq_zero
  rw [hzE, zero_add] at hE
  exact hE.trans ((Algebra.TensorProduct.comm k E A).trdeg_eq.trans hA.symm)

variable {σ : Type*}

/-- The original coordinate elements generate the extended chart over
its extended coefficient field. -/
theorem tensor_coordinates_adjoin_eq_top (x : σ → A)
    (hx : Algebra.adjoin k (Set.range x) = ⊤) :
    Algebra.adjoin E (Set.range (fun i => (1 : E) ⊗ₜ[k] x i)) = ⊤ := by
  simpa only [← Set.range_comp, Function.comp_def] using
    Algebra.TensorProduct.adjoin_one_tmul_image_eq_top (A := E) (Set.range x) hx

/-- The actual original coordinate inclusion into the extended chart
preserves nonzero coordinates. -/
theorem tensor_coordinate_ne_zero {x : A} (hx : x ≠ 0) :
    (1 : E) ⊗ₜ[k] x ≠ 0 := by
  have hi := Algebra.TensorProduct.includeRight_injective (R := k) (A := E) (B := A)
    (algebraMap k E).injective
  exact fun h => hx (hi (h.trans (map_zero Algebra.TensorProduct.includeRight).symm))

/-- Extending the original equation's coefficients preserves its
vanishing at the extended original coordinates. -/
theorem tensor_coordinate_equation (x : σ → A) (f : MvPolynomial σ k)
    (hroot : MvPolynomial.aeval x f = 0) :
    MvPolynomial.aeval (fun i => (1 : E) ⊗ₜ[k] x i)
      (MvPolynomial.map (algebraMap k E) f) = 0 := by
  let g : A →ₐ[k] E ⊗[k] A := Algebra.TensorProduct.includeRight
  have h := congrArg g hroot
  rw [MvPolynomial.comp_aeval_apply, map_zero] at h
  rw [MvPolynomial.aeval_def, MvPolynomial.eval₂_map, ← IsScalarTower.algebraMap_eq k E (E ⊗[k] A)]
  exact h

end DimensionFourDependence
