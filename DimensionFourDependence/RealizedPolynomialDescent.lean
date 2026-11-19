import DimensionFourDependence.TensorPolynomialDescent

/-! # Coefficient descent on an actual compatible geometric field branch

The original source and closed-field embeddings specify all coefficient
actions, including the action on an actual intermediate field of the
geometric constants. Their compatibility constructs the tensor comparison
needed for descent; no auxiliary scalar actions are supplied.
-/

namespace DimensionFourDependence

open MvPolynomial

variable {K C M E G : Type*} [Field K] [Field C] [CharZero C] [Field M] [Field E] [Field G]
    [Algebra K C] [Algebra K M] [Algebra C M] [Algebra K E] [Algebra K G] [Algebra E G]
    {n : ℕ}

/-- Every polynomial on an actual algebraic geometric coefficient
branch representing an original source function descends to the original
relatively closed field, with its actual coefficient map and source value. -/
theorem compatible_realized_polynomial_expansion_descends
    (g : C →ₐ[K] E) (f : M →ₐ[K] G)
    (hcomp : ∀ c : C, algebraMap E G (g c) = f (algebraMap C M c))
    (F : IntermediateField g.fieldRange E) (hF : Algebra.IsAlgebraic g.fieldRange F)
    (hclosed : algebraicClosure C M = ⊥) (x : Fin n → M) (hx : AlgebraicIndependent C x)
    (P : MvPolynomial (Fin n) F) (y : M)
    (hvalue : aeval (fun i => f (x i)) P = f y) :
    ∃ Q : MvPolynomial (Fin n) C,
      MvPolynomial.map ((algebraMap g.fieldRange F).comp g.equivFieldRange.toRingHom) Q = P ∧
        aeval x Q = y := by
  let cF : C →+* F := (algebraMap g.fieldRange F).comp g.equivFieldRange.toRingHom
  let : Algebra C F := cF.toAlgebra
  let : Algebra M G := f.toRingHom.toAlgebra
  let : Algebra C G := ((algebraMap E G).comp g.toRingHom).toAlgebra
  let : IsScalarTower C M G := IsScalarTower.of_algebraMap_eq (by intro c; exact hcomp c)
  let : IsScalarTower C F G := IsScalarTower.of_algebraMap_eq (by intro c; rfl)
  have halg : Algebra.IsAlgebraic C F :=
    (Algebra.isAlgebraic_ringHom_iff_of_comp_eq g.equivFieldRange.toRingEquiv (RingEquiv.refl F)
      (by apply RingHom.ext; intro c; rfl)).mp hF
  let : Algebra.IsAlgebraic C F := halg
  obtain ⟨Q, hQ, hy⟩ := relatively_closed_polynomial_expansion_descends (C := C) (M := M) (E := F)
    (G := G) hclosed x hx P y hvalue
  exact ⟨Q, hQ, hy⟩

end DimensionFourDependence
