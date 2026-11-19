import DimensionFourDependence.IntegralCoordinateFieldGeneration

/-! # Coordinate generation at every actual normalization prime -/

namespace DimensionFourDependence

variable {E J A σ : Type*} [Field E] [Field J] [CommRing A]
  [Algebra E A]

/-- The canonical ring structure on normalization, before specializing its base. -/
@[instance_reducible]
noncomputable def normalizationRingCommRingInstance : CommRing (normalizationRing A) :=
  inferInstance

/-- The actual prime quotient fraction field with its canonical field structure. -/
@[instance_reducible]
noncomputable def normalizationPrimeResidueFieldInstance
    (Q : Ideal (normalizationRing A)) [Q.IsPrime] :
    Field (FractionRing (normalizationRing A ⧸ Q)) := inferInstance

/-- The original coordinate action on the canonical residue fraction field. -/
@[instance_reducible]
noncomputable def normalizationPrimeResidueCoordinateAlgebra
    (Q : Ideal (normalizationRing A)) [Q.IsPrime] :
    Algebra A (FractionRing (normalizationRing A ⧸ Q)) := inferInstance

/-- The canonical coefficient action on the quotient fraction field of
an actual normalization prime, constructed before specialization to a chart. -/
@[instance_reducible]
noncomputable def normalizationPrimeResidueCoefficientAlgebra
    (Q : Ideal (normalizationRing A)) [Q.IsPrime] :
    Algebra E (FractionRing (normalizationRing A ⧸ Q)) := inferInstance

/-- This canonical residue coefficient action retains the original
coordinate-ring action on the quotient fraction field. -/
theorem normalizationPrimeResidueCoefficientAlgebra_source_tower
    (Q : Ideal (normalizationRing A)) [Q.IsPrime] :
    @IsScalarTower E A (FractionRing (normalizationRing A ⧸ Q)) _
      (normalizationPrimeResidueCoordinateAlgebra Q).toSMul
      (normalizationPrimeResidueCoefficientAlgebra (E := E) Q).toSMul := by
  let : Algebra A (FractionRing (normalizationRing A ⧸ Q)) := normalizationPrimeResidueCoordinateAlgebra Q
  let : Algebra E (FractionRing (normalizationRing A ⧸ Q)) := normalizationPrimeResidueCoefficientAlgebra Q
  infer_instance

variable {C : Type*} [Field C] [Algebra C E] [Algebra C A] [IsScalarTower C E A]

/-- Passing to normalization-prime residues preserves the entire
original tower of coefficient fields. -/
theorem normalizationPrimeResidueCoefficientAlgebra_coefficient_tower
    (Q : Ideal (normalizationRing A)) [Q.IsPrime] :
    @IsScalarTower C E (FractionRing (normalizationRing A ⧸ Q)) _
      (normalizationPrimeResidueCoefficientAlgebra (E := E) Q).toSMul
      (normalizationPrimeResidueCoefficientAlgebra (E := C) Q).toSMul := by
  let : Algebra E (FractionRing (normalizationRing A ⧸ Q)) := normalizationPrimeResidueCoefficientAlgebra Q
  let : Algebra C (FractionRing (normalizationRing A ⧸ Q)) := normalizationPrimeResidueCoefficientAlgebra Q
  infer_instance

/-- The quotient of the canonical normalization by any prime is
integral over the original coordinate ring, with its original action. -/
theorem normalization_prime_quotient_isIntegral
    (Q : Ideal (normalizationRing A)) :
    Algebra.IsIntegral A (normalizationRing A ⧸ Q) := by
  constructor
  intro z
  obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective z
  have hb : IsIntegral A b := integralClosure.isIntegral (R := A) (A := FractionRing A) b
  exact hb.map
    (IsScalarTower.toAlgHom A (normalizationRing A) (normalizationRing A ⧸ Q))

/-- Every actual prime residue fraction field of the normalization is
algebraic over any field making its original coefficients and coordinate
residues algebraic. The normalization and prime quotient are constructed,
and their integrality is proved rather than assumed. -/
theorem normalization_prime_residue_fraction_field_isAlgebraic
    (Q : Ideal (normalizationRing A)) [Q.IsPrime]
    [Algebra J (FractionRing (normalizationRing A ⧸ Q))]
    (x : σ → A) (hgen : Algebra.adjoin E (Set.range x) = ⊤)
    (hcoeff : ∀ e : E, IsAlgebraic J
      (algebraMap E (FractionRing (normalizationRing A ⧸ Q)) e))
    (hcoord : ∀ i, IsAlgebraic J
      (algebraMap A (FractionRing (normalizationRing A ⧸ Q)) (x i))) :
    Algebra.IsAlgebraic J (FractionRing (normalizationRing A ⧸ Q)) := by
  let : Algebra.IsIntegral A (normalizationRing A ⧸ Q) :=
    normalization_prime_quotient_isIntegral Q
  exact integral_coordinate_fraction_field_isAlgebraic
    (B := normalizationRing A ⧸ Q) x hgen hcoeff hcoord

end DimensionFourDependence
