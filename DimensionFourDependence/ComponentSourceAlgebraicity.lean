import DimensionFourDependence.ComponentGenericPoint
import Mathlib.FieldTheory.AlgebraicClosure

/-! # Actual geometric component fields are algebraic over the embedded source

The quotient's original generic coordinates generate its entire fraction
field. Algebraic extension of the output constants therefore makes each
actual component field algebraic over its compatible original source.
-/

namespace DimensionFourDependence

open MvPolynomial

set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 100000

/-- The original generic coordinates generate the whole prime quotient
fraction field over its actual coefficient field. -/
theorem primeQuotientCoordinate_adjoin_eq_top
    {E : Type*} [Field E] {n : ℕ}
    (P : Ideal (MvPolynomial (Fin n) E)) [P.IsPrime] :
    IntermediateField.adjoin E (Set.range (primeQuotientCoordinate P)) = ⊤ := by
  let A := IntermediateField.adjoin E (Set.range (primeQuotientCoordinate P))
  have hpoly (p : MvPolynomial (Fin n) E) : aeval (primeQuotientCoordinate P) p ∈ A := by
    induction p using MvPolynomial.induction_on with
    | C c => simpa using A.algebraMap_mem c
    | add p q hp hq => simpa only [map_add] using A.add_mem hp hq
    | mul_X p i hp =>
      rw [map_mul, aeval_X]
      exact A.mul_mem hp (IntermediateField.subset_adjoin E _ ⟨i, rfl⟩)
  have hquot (q : MvPolynomial (Fin n) E ⧸ P) :
      algebraMap _ (FractionRing (MvPolynomial (Fin n) E ⧸ P)) q ∈ A := by
    obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective q
    simpa only [primeQuotientCoordinate_aeval] using hpoly p
  apply top_unique
  intro u _
  obtain ⟨a, b, _hb, rfl⟩ := IsFractionRing.div_surjective (A := MvPolynomial (Fin n) E ⧸ P) u
  exact A.div_mem (hquot a) (hquot b)

/-- If the geometric constants are algebraic over the output base,
and the actual source coordinates generate a component field, that
component field is algebraic over the compatible embedded source. -/
theorem generated_component_isAlgebraic_over_embedded_source
    {M S E G σ : Type*} [Field M] [Field S] [Field E] [Field G]
    [Algebra M S] [Algebra M E] [Algebra E G] [Algebra M G]
    [IsScalarTower M E G] [Algebra.IsAlgebraic M E]
    (f : S →ₐ[M] G) (x : σ → S)
    (hgen : IntermediateField.adjoin E (Set.range (fun i => f (x i))) = ⊤) :
    letI : Algebra S G := f.toRingHom.toAlgebra
    Algebra.IsAlgebraic S G := by
  letI : Algebra S G := f.toRingHom.toAlgebra
  letI : IsScalarTower M S G := IsScalarTower.of_algebraMap_eq (fun m => (f.commutes m).symm)
  have hE (e : E) : IsAlgebraic S (algebraMap E G e) :=
    ((Algebra.IsAlgebraic.isAlgebraic (R := M) e).algHom
      (IsScalarTower.toAlgHom M E G)).tower_top S
  let A : IntermediateField E G :=
    { (algebraicClosure S G).toSubfield with
      algebraMap_mem' := fun e => mem_algebraicClosure_iff.mpr (hE e) }
  have hle : IntermediateField.adjoin E (Set.range (fun i => f (x i))) ≤ A := by
    apply IntermediateField.adjoin_le_iff.mpr
    rintro _ ⟨i, rfl⟩
    exact mem_algebraicClosure_iff.mpr (isAlgebraic_algebraMap (R := S) (A := G) (x i))
  rw [hgen] at hle
  refine ⟨fun u => mem_algebraicClosure_iff.mp ?_⟩
  exact hle (show u ∈ (⊤ : IntermediateField E G) from trivial)

end DimensionFourDependence
