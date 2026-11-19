import DimensionFourDependence.GeometricCoefficientRealization

/-! # Algebraic coefficient extensions for the constructed realization

The realized coefficient embedding preserves the original scalars and
all four output coordinates, hence the full output field. If the
geometric constants are algebraic over that output field, they are
algebraic over the realized coefficient field as well.
-/

namespace DimensionFourDependence

open MvPolynomial

variable {K E G : Type*} [Field K] [CharZero K] [Field E] [Algebra K E]
    [Field G] [Algebra E G]

/-- The realized coefficient map is an algebra homomorphism over the
original scalar field, as required for extending coordinate derivations. -/
noncomputable def FiberCoefficientRealization.coefficientAlgHom
    {p : Equiv.Perm (Fin 4)} {Y : Fin 3 → FractionRing (MvPolynomial (Fin 4) K)}
    {hY : AlgebraicIndependent K Y} {h c q k : coefficientField (K := K) Y}
    {x : Fin 4 → G} {y : Fin 4 → E} (R : FiberCoefficientRealization p Y hY h c q k x y) :
    coefficientField (K := K) Y →ₐ[K] E where
  toRingHom := R.coefficientMap
  commutes' := R.scalar_image

/-- The actual scalar compatibility supplies the tower for extending
the coefficient-coordinate derivations. -/
theorem FiberCoefficientRealization.scalarTower
    {p : Equiv.Perm (Fin 4)} {Y : Fin 3 → FractionRing (MvPolynomial (Fin 4) K)}
    {hY : AlgebraicIndependent K Y} {h c q k : coefficientField (K := K) Y}
    {x : Fin 4 → G} {y : Fin 4 → E} (R : FiberCoefficientRealization p Y hY h c q k x y) :
    letI : Algebra (coefficientField (K := K) Y) E := R.coefficientMap.toAlgebra
    IsScalarTower K (coefficientField (K := K) Y) E := by
  let : Algebra (coefficientField (K := K) Y) E := R.coefficientMap.toAlgebra
  exact IsScalarTower.of_algebraMap_eq (fun r => (R.scalar_image r).symm)

section

variable (H : Fin 4 → FractionRing (MvPolynomial (Fin 4) K))
    (hrank : (rationalJacobian H).rank = 3) (W : FiberEquationWitness H)
    (h c q k : coefficientField (K := K) (fun i : Fin 3 => H (W.chart i.castSucc)))
    (hh : (h : FractionRing (MvPolynomial (Fin 4) K)) = H (W.chart 3))
    [Algebra (fullOutputField (K := K) H) E]
    [IsScalarTower K (fullOutputField (K := K) H) E]
    (x : Fin 4 → G)
    (R : FiberCoefficientRealization W.chart (fun i : Fin 3 => H (W.chart i.castSucc))
      W.independent h c q k x
      (fun j => algebraMap (fullOutputField (K := K) H) E (fullOutputCoordinate (K := K) H j)))

include hh

/-- Images of the selected outputs and the last output force the
realized coefficient embedding to preserve the full output field. -/
theorem FiberCoefficientRealization.output_field_compatibility
    (m : fullOutputField (K := K) H) :
    R.coefficientMap (fullOutputCoefficientHom H hrank W.chart W.independent m) =
      algebraMap (fullOutputField (K := K) H) E m := by
  let M := fullOutputField (K := K) H
  let L := coefficientField (K := K) (fun i : Fin 3 => H (W.chart i.castSucc))
  let φ : M →ₐ[K] E := R.coefficientAlgHom.comp (fullOutputCoefficientHom H hrank W.chart W.independent)
  let ψ : M →ₐ[K] E := IsScalarTower.toAlgHom K M E
  have he : φ = ψ := by
    apply IntermediateField.adjoin_algHom_ext K
    rintro z ⟨j, rfl⟩
    obtain ⟨i, rfl⟩ := W.chart.surjective j
    refine Fin.lastCases ?_ (fun j => ?_) i
    · change R.coefficientMap (fullOutputCoefficientHom H hrank W.chart W.independent
        (fullOutputCoordinate (K := K) H (W.chart 3))) =
        algebraMap M E (fullOutputCoordinate (K := K) H (W.chart 3))
      have hlast : fullOutputCoefficientHom H hrank W.chart W.independent
          (fullOutputCoordinate (K := K) H (W.chart 3)) = h := by
        apply Subtype.ext
        exact hh.symm
      rw [hlast]
      exact R.last_output_image
    · change R.coefficientMap (coefficientCoordinate (K := K)
        (fun i : Fin 3 => H (W.chart i.castSucc)) j) =
        algebraMap M E (fullOutputCoordinate (K := K) H (W.chart j.castSucc))
      exact R.coordinate_image j
  exact congrArg (fun f : M →ₐ[K] E => f m) he

include hrank in
/-- Algebraicity of the geometric constants over the full output
field supplies the actual algebraic coefficient extension for line integration. -/
theorem FiberCoefficientRealization.algebraic_extension
    [Algebra.IsAlgebraic (fullOutputField (K := K) H) E] :
    letI : Algebra (coefficientField (K := K) (fun i : Fin 3 => H (W.chart i.castSucc))) E :=
      R.coefficientMap.toAlgebra
    Algebra.IsAlgebraic (coefficientField (K := K) (fun i : Fin 3 => H (W.chart i.castSucc))) E := by
  let M := fullOutputField (K := K) H
  let L := coefficientField (K := K) (fun i : Fin 3 => H (W.chart i.castSucc))
  let : Algebra M L := fullOutputCoefficientAlgebra H hrank W.chart W.independent
  let : Algebra L E := R.coefficientMap.toAlgebra
  let : IsScalarTower M L E := IsScalarTower.of_algebraMap_eq (fun m =>
    (R.output_field_compatibility H hrank W h c q k hh x m).symm)
  exact Algebra.IsAlgebraic.tower_top (K := M) (L := L)

end

end DimensionFourDependence
