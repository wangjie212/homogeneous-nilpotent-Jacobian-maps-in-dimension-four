import DimensionFourDependence.IndependentRationalProjection

/-! # The actual iterated rational projection field from independent coordinates

The first coordinate specifies the embedded rational parameter field.
Independence makes the second coordinate transcendental over it, so its
actual polynomial evaluation extends to the full rational function field.
Both coordinate values, the polynomial base and the original constants
are retained by the constructed field action.
-/

namespace DimensionFourDependence

set_option synthInstance.maxHeartbeats 100000
set_option maxHeartbeats 1000000

variable {k L : Type*} [Field k] [Field L] [Algebra k L]
  [Algebra (RatFunc k) L] [IsScalarTower k (RatFunc k) L]

/-- The original independent coordinates construct the entire iterated
rational projection field embedding, with no vanishing hypothesis on the
outer projection coordinate. -/
noncomputable def independentProjectionFieldHom
    (u w : L) (h : AlgebraicIndependent k ![u, w])
    (hX : algebraMap (RatFunc k) L RatFunc.X = u) :
    RatFunc (RatFunc k) →ₐ[RatFunc k] L :=
  IsLocalization.liftAlgHom (M := nonZeroDivisors (Polynomial (RatFunc k)))
    (f := Polynomial.aeval w) fun p => by
      apply isUnit_iff_ne_zero.mpr
      intro hp
      exact independent_pair_transcendental_rational_parameter u w h hX
        ⟨p, mem_nonZeroDivisors_iff_ne_zero.mp p.property, hp⟩

/-- Every projection-base polynomial retains its actual evaluation at
the original outer coordinate. -/
theorem independentProjectionFieldHom_polynomial
    (u w : L) (h : AlgebraicIndependent k ![u, w])
    (hX : algebraMap (RatFunc k) L RatFunc.X = u) (P : Polynomial (RatFunc k)) :
    independentProjectionFieldHom u w h hX
      (algebraMap (Polynomial (RatFunc k)) (RatFunc (RatFunc k)) P) = Polynomial.aeval w P :=
  IsLocalization.lift_eq _ _

/-- The actual outer projection variable has its original coordinate value. -/
theorem independentProjectionFieldHom_X
    (u w : L) (h : AlgebraicIndependent k ![u, w])
    (hX : algebraMap (RatFunc k) L RatFunc.X = u) :
    independentProjectionFieldHom u w h hX RatFunc.X = w := by
  rw [← RatFunc.algebraMap_X, independentProjectionFieldHom_polynomial, Polynomial.aeval_X]

/-- The actual inner parameter retains its original first-coordinate value. -/
theorem independentProjectionFieldHom_inner_X
    (u w : L) (h : AlgebraicIndependent k ![u, w])
    (hX : algebraMap (RatFunc k) L RatFunc.X = u) :
    independentProjectionFieldHom u w h hX
      (algebraMap (RatFunc k) (RatFunc (RatFunc k)) RatFunc.X) = u := by
  rw [(independentProjectionFieldHom u w h hX).commutes, hX]

/-- The compatible polynomial-base action is actual original evaluation. -/
@[instance_reducible]
noncomputable def independentProjectionPolynomialAlgebra (w : L) :
    Algebra (Polynomial (RatFunc k)) L := (Polynomial.aeval w).toRingHom.toAlgebra

/-- The constructed actual full projection-field action. -/
@[instance_reducible]
noncomputable def independentProjectionFieldAlgebra
    (u w : L) (h : AlgebraicIndependent k ![u, w])
    (hX : algebraMap (RatFunc k) L RatFunc.X = u) : Algebra (RatFunc (RatFunc k)) L :=
  (independentProjectionFieldHom u w h hX).toRingHom.toAlgebra

/-- The full projection action preserves its actual rational coefficient field. -/
theorem independentProjectionFieldAlgebra_scalarTower
    (u w : L) (h : AlgebraicIndependent k ![u, w])
    (hX : algebraMap (RatFunc k) L RatFunc.X = u) :
    let : Algebra (RatFunc (RatFunc k)) L := independentProjectionFieldAlgebra u w h hX
    IsScalarTower (RatFunc k) (RatFunc (RatFunc k)) L := by
  let : Algebra (RatFunc (RatFunc k)) L := independentProjectionFieldAlgebra u w h hX
  exact IsScalarTower.of_algebraMap_eq
    (fun c => ((independentProjectionFieldHom u w h hX).commutes c).symm)

/-- The actual polynomial evaluation and actual full projection field
action agree on every element of the projection base ring. -/
theorem independentProjectionFieldAlgebra_polynomial_scalarTower
    (u w : L) (h : AlgebraicIndependent k ![u, w])
    (hX : algebraMap (RatFunc k) L RatFunc.X = u) :
    let : Algebra (Polynomial (RatFunc k)) L := independentProjectionPolynomialAlgebra w
    let : Algebra (RatFunc (RatFunc k)) L := independentProjectionFieldAlgebra u w h hX
    IsScalarTower (Polynomial (RatFunc k)) (RatFunc (RatFunc k)) L := by
  let : Algebra (Polynomial (RatFunc k)) L := independentProjectionPolynomialAlgebra w
  let : Algebra (RatFunc (RatFunc k)) L := independentProjectionFieldAlgebra u w h hX
  exact IsScalarTower.of_algebraMap_eq
    (fun P => (independentProjectionFieldHom_polynomial u w h hX P).symm)

/-- The iterated field action retains the original coefficient field. -/
theorem independentProjectionFieldAlgebra_original_scalarTower
    (u w : L) (h : AlgebraicIndependent k ![u, w])
    (hX : algebraMap (RatFunc k) L RatFunc.X = u) :
    let : Algebra (RatFunc (RatFunc k)) L := independentProjectionFieldAlgebra u w h hX
    IsScalarTower k (RatFunc (RatFunc k)) L := by
  let : Algebra (RatFunc (RatFunc k)) L := independentProjectionFieldAlgebra u w h hX
  let : IsScalarTower (RatFunc k) (RatFunc (RatFunc k)) L :=
    independentProjectionFieldAlgebra_scalarTower u w h hX
  exact IsScalarTower.to₁₃₄ k (RatFunc k) (RatFunc (RatFunc k)) L

end DimensionFourDependence
