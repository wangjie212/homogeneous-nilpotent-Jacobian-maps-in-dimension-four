import DimensionFourDependence.FullOutputField

/-! # The actual source prime over the full output field

The full output field embeds in the verified coefficient field. This is
an algebraic extension, and the actual four-coordinate source prime is
a component of the full-output generic fiber after this extension.
-/

namespace DimensionFourDependence

open MvPolynomial

variable {K : Type*} [Field K] [CharZero K]

/-- Inclusion of the full output field in the actual coefficient field. -/
noncomputable def fullOutputCoefficientHom
    (H : Fin 4 → FractionRing (MvPolynomial (Fin 4) K))
    (hrank : (rationalJacobian H).rank = 3) (p : Equiv.Perm (Fin 4))
    (hY : AlgebraicIndependent K (fun i : Fin 3 => H (p i.castSucc))) :
    fullOutputField (K := K) H →ₐ[K]
      coefficientField (K := K) (fun i : Fin 3 => H (p i.castSucc)) where
  toFun a := ⟨a, fullOutputField_mem_coefficientField H hrank p hY a⟩
  map_zero' := Subtype.ext rfl
  map_one' := Subtype.ext rfl
  map_add' _ _ := Subtype.ext rfl
  map_mul' _ _ := Subtype.ext rfl
  commutes' _ := Subtype.ext rfl

/-- The coefficient algebra induced by the actual inclusions in the source field. -/
@[instance_reducible] noncomputable def fullOutputCoefficientAlgebra
    (H : Fin 4 → FractionRing (MvPolynomial (Fin 4) K))
    (hrank : (rationalJacobian H).rank = 3) (p : Equiv.Perm (Fin 4))
    (hY : AlgebraicIndependent K (fun i : Fin 3 => H (p i.castSucc))) :
    Algebra (fullOutputField (K := K) H)
      (coefficientField (K := K) (fun i : Fin 3 => H (p i.castSucc))) :=
  (fullOutputCoefficientHom H hrank p hY).toRingHom.toAlgebra

/-- The actual coefficient field is algebraic over `K(H)`. -/
theorem fullOutputCoefficient_isAlgebraic
    (H : Fin 4 → FractionRing (MvPolynomial (Fin 4) K))
    (hrank : (rationalJacobian H).rank = 3) (p : Equiv.Perm (Fin 4))
    (hY : AlgebraicIndependent K (fun i : Fin 3 => H (p i.castSucc))) :
    letI := fullOutputCoefficientAlgebra H hrank p hY
    Algebra.IsAlgebraic (fullOutputField (K := K) H)
      (coefficientField (K := K) (fun i : Fin 3 => H (p i.castSucc))) := by
  let := fullOutputCoefficientAlgebra H hrank p hY
  let L := coefficientField (K := K) (fun i : Fin 3 => H (p i.castSucc))
  let M := fullOutputField (K := K) H
  let : IsScalarTower M L (FractionRing (MvPolynomial (Fin 4) K)) :=
    IsScalarTower.of_algebraMap_eq (by intro b; rfl)
  constructor
  intro a
  apply (isAlgebraic_algebraMap_iff (algebraMap L (FractionRing (MvPolynomial (Fin 4) K))).injective).mp
  exact (fullOutput_algebraic_iff_coefficientField H hrank p hY a).mpr a.property

/-- The actual source relation prime over `L` is a component of the
full-output generic fiber after extending from `K(H)` to `L`. -/
theorem fiber_witness_prime_component_over_full_outputs
    (H : Fin 4 → FractionRing (MvPolynomial (Fin 4) K))
    (hrank : (rationalJacobian H).rank = 3) (W : FiberEquationWitness H) :
    letI := fullOutputCoefficientAlgebra H hrank W.chart W.independent
    fiberVanishingIdeal
      (L := coefficientField (K := K) (fun i : Fin 3 => H (W.chart i.castSucc)))
      (rationalCoordinate (K := K) (n := 4)) ∈
    (extendCoefficientIdeal
      (coefficientField (K := K) (fun i : Fin 3 => H (W.chart i.castSucc)))
      (fiberVanishingIdeal (L := fullOutputField (K := K) H)
        (rationalCoordinate (K := K) (n := 4)))).minimalPrimes := by
  let := fullOutputCoefficientAlgebra H hrank W.chart W.independent
  let L := coefficientField (K := K) (fun i : Fin 3 => H (W.chart i.castSucc))
  let M := fullOutputField (K := K) H
  let : IsScalarTower M L (FractionRing (MvPolynomial (Fin 4) K)) :=
    IsScalarTower.of_algebraMap_eq (by intro b; rfl)
  let : Algebra.IsAlgebraic M L := fullOutputCoefficient_isAlgebraic H hrank W.chart W.independent
  exact fiber_prime_minimal_after_algebraic_coefficients _

end DimensionFourDependence
