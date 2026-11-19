import DimensionFourDependence.ResidueIndependentProjectionField

/-! # Compatible actual polynomial actions for the independent residue projection

The rational parameter is regular in the original local ring and the
outer polynomial variable evaluates at the other original coordinate.
The local polynomial action, its function-field action and the complete
iterated rational-field action retain the same actual values and the
original constant field.
-/

namespace DimensionFourDependence

set_option synthInstance.maxHeartbeats 100000
set_option maxHeartbeats 2000000

variable {k B L : Type*} [Field k] [CommRing B] [IsLocalRing B] [Algebra k B]
  [Field L] [Algebra B L] [Algebra k L] [IsScalarTower k B L]

/-- The actual outer polynomial base acts regularly on the original
local ring, with its rational coefficients supplied by the residue parameter. -/
@[instance_reducible]
noncomputable def residueProjectionPolynomialAlgebra
    (u : B) (hu : Transcendental k (IsLocalRing.residue B u)) (w : B) :
    Algebra (Polynomial (RatFunc k)) B := by
  let : Algebra (RatFunc k) B := residueParameterFieldAlgebra u hu
  exact (Polynomial.aeval w).toRingHom.toAlgebra

/-- The same actual polynomial action on the specified function field,
through the entire original local-ring inclusion. -/
@[instance_reducible]
noncomputable def residueProjectionPolynomialTargetAlgebra
    (u : B) (hu : Transcendental k (IsLocalRing.residue B u)) (w : B) :
    Algebra (Polynomial (RatFunc k)) L := by
  let : Algebra (Polynomial (RatFunc k)) B := residueProjectionPolynomialAlgebra u hu w
  exact ((algebraMap B L).comp (algebraMap (Polynomial (RatFunc k)) B)).toAlgebra

/-- The actual polynomial variable retains the original local coordinate. -/
theorem residueProjectionPolynomialAlgebra_X
    (u : B) (hu : Transcendental k (IsLocalRing.residue B u)) (w : B) :
    let : Algebra (Polynomial (RatFunc k)) B := residueProjectionPolynomialAlgebra u hu w
    algebraMap (Polynomial (RatFunc k)) B Polynomial.X = w := by
  let : Algebra (RatFunc k) B := residueParameterFieldAlgebra u hu
  let : Algebra (Polynomial (RatFunc k)) B := residueProjectionPolynomialAlgebra u hu w
  change Polynomial.aeval w Polynomial.X = w
  exact Polynomial.aeval_X w

/-- The original rational coefficient field is unchanged by polynomial evaluation. -/
theorem residueProjectionPolynomialAlgebra_parameter_scalarTower
    (u : B) (hu : Transcendental k (IsLocalRing.residue B u)) (w : B) :
    let : Algebra (RatFunc k) B := residueParameterFieldAlgebra u hu
    let : Algebra (Polynomial (RatFunc k)) B := residueProjectionPolynomialAlgebra u hu w
    IsScalarTower (RatFunc k) (Polynomial (RatFunc k)) B := by
  let : Algebra (RatFunc k) B := residueParameterFieldAlgebra u hu
  let : Algebra (Polynomial (RatFunc k)) B := residueProjectionPolynomialAlgebra u hu w
  exact IsScalarTower.of_algebraMap_eq (fun c => ((Polynomial.aeval w).commutes c).symm)

/-- The actual regular polynomial base retains the original constants. -/
theorem residueProjectionPolynomialAlgebra_original_scalarTower
    (u : B) (hu : Transcendental k (IsLocalRing.residue B u)) (w : B) :
    let : Algebra (Polynomial (RatFunc k)) B := residueProjectionPolynomialAlgebra u hu w
    IsScalarTower k (Polynomial (RatFunc k)) B := by
  let : Algebra (RatFunc k) B := residueParameterFieldAlgebra u hu
  let : IsScalarTower k (RatFunc k) B := residueParameterFieldAlgebra_scalarTower u hu
  let : Algebra (Polynomial (RatFunc k)) B := residueProjectionPolynomialAlgebra u hu w
  let : IsScalarTower (RatFunc k) (Polynomial (RatFunc k)) B :=
    residueProjectionPolynomialAlgebra_parameter_scalarTower u hu w
  exact IsScalarTower.to₁₃₄ k (RatFunc k) (Polynomial (RatFunc k)) B

omit [Algebra k L] [IsScalarTower k B L] in
/-- Every original regular polynomial value has the same image in the
specified function field. -/
theorem residueProjectionPolynomialTargetAlgebra_source_scalarTower
    (u : B) (hu : Transcendental k (IsLocalRing.residue B u)) (w : B) :
    let : Algebra (Polynomial (RatFunc k)) B := residueProjectionPolynomialAlgebra u hu w
    let : Algebra (Polynomial (RatFunc k)) L := residueProjectionPolynomialTargetAlgebra (L := L) u hu w
    IsScalarTower (Polynomial (RatFunc k)) B L := by
  let : Algebra (Polynomial (RatFunc k)) B := residueProjectionPolynomialAlgebra u hu w
  let : Algebra (Polynomial (RatFunc k)) L := residueProjectionPolynomialTargetAlgebra (L := L) u hu w
  exact IsScalarTower.of_algebraMap_eq (fun _ => rfl)

/-- The actual polynomial-base action on the target function field
retains the original constant-field action. -/
theorem residueProjectionPolynomialTargetAlgebra_original_scalarTower
    (u : B) (hu : Transcendental k (IsLocalRing.residue B u)) (w : B) :
    let : Algebra (Polynomial (RatFunc k)) L := residueProjectionPolynomialTargetAlgebra (L := L) u hu w
    IsScalarTower k (Polynomial (RatFunc k)) L := by
  let : Algebra (Polynomial (RatFunc k)) B := residueProjectionPolynomialAlgebra u hu w
  let : IsScalarTower k (Polynomial (RatFunc k)) B :=
    residueProjectionPolynomialAlgebra_original_scalarTower u hu w
  let : Algebra (Polynomial (RatFunc k)) L := residueProjectionPolynomialTargetAlgebra (L := L) u hu w
  let : IsScalarTower (Polynomial (RatFunc k)) B L :=
    residueProjectionPolynomialTargetAlgebra_source_scalarTower (L := L) u hu w
  exact IsScalarTower.to₁₂₄ k (Polynomial (RatFunc k)) B L

/-- The actual regular polynomial base and the constructed iterated
function field act compatibly through their original coordinate values. -/
theorem independentResidueProjectionFieldAlgebra_polynomial_scalarTower
    (u w : B) (hu : Transcendental k (IsLocalRing.residue B u))
    (h : AlgebraicIndependent k ![algebraMap B L u, algebraMap B L w]) :
    let : Algebra (Polynomial (RatFunc k)) L := residueProjectionPolynomialTargetAlgebra (L := L) u hu w
    let : Algebra (RatFunc (RatFunc k)) L := independentResidueProjectionFieldAlgebra u w hu h
    IsScalarTower (Polynomial (RatFunc k)) (RatFunc (RatFunc k)) L := by
  let : Algebra (RatFunc k) B := residueParameterFieldAlgebra u hu
  let : Algebra (RatFunc k) L := residueParameterTargetFieldAlgebra (L := L) u hu
  let : IsScalarTower (RatFunc k) B L := residueParameterTargetFieldAlgebra_scalarTower (L := L) u hu
  let : Algebra (Polynomial (RatFunc k)) B := residueProjectionPolynomialAlgebra u hu w
  let : Algebra (Polynomial (RatFunc k)) L := residueProjectionPolynomialTargetAlgebra (L := L) u hu w
  let : Algebra (RatFunc (RatFunc k)) L := independentResidueProjectionFieldAlgebra u w hu h
  apply IsScalarTower.of_algebraMap_eq
  intro P
  change algebraMap B L (Polynomial.aeval w P) = independentResidueProjectionFieldHom u w hu h
    (algebraMap (Polynomial (RatFunc k)) (RatFunc (RatFunc k)) P)
  rw [independentResidueProjectionFieldHom_polynomial]
  exact (Polynomial.aeval_algHom_apply (IsScalarTower.toAlgHom (RatFunc k) B L) w P).symm

end DimensionFourDependence
