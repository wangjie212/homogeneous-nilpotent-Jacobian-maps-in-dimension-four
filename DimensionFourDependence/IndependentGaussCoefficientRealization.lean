import DimensionFourDependence.PrimitiveRationalVector
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure

/-! # Algebraic Gauss coefficients at a source-independent parameter

Use the algebraic closure of the rational function field of the given
source-coordinate field. Its rational variable is transcendental over
that entire field. The actual algebraic coefficient extension embeds
there while preserving the closed Gauss parameter and all original
constants. Neither disjointness nor a tensor-domain assumption is needed.
-/

namespace DimensionFourDependence

set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 100000

variable {K L : Type*} [Field K] [Field L] [Algebra K L]

/-- A parameter transcendental over the original constants realizes
their whole rational function field with that exact parameter value. -/
noncomputable def transcendentalParameterFieldHom
    (t : L) (ht : Transcendental K t) : RatFunc K →ₐ[K] L :=
  IsLocalization.liftAlgHom (M := nonZeroDivisors (Polynomial K))
    (f := Polynomial.aeval t) fun p => by
      apply isUnit_iff_ne_zero.mpr
      intro hp
      exact ht ⟨p, mem_nonZeroDivisors_iff_ne_zero.mp p.property, hp⟩

/-- The constructed rational function field embedding retains the
specified independent parameter. -/
theorem transcendentalParameterFieldHom_X (t : L) (ht : Transcendental K t) :
    transcendentalParameterFieldHom t ht RatFunc.X = t := by
  rw [← RatFunc.algebraMap_X]
  simp only [transcendentalParameterFieldHom, IsLocalization.liftAlgHom_apply, IsLocalization.lift_eq]
  exact Polynomial.aeval_X t

variable (F : Type*) [Field F]

/-- The source-coordinate field acts on the chosen independent
parameter closure through its original coefficient embedding. -/
@[instance_reducible]
noncomputable def independentParameterClosureAlgebra :
    Algebra F (AlgebraicClosure (RatFunc F)) :=
  inferInstance

variable (K) [Algebra K F]

/-- The original constants retain their specified source-coordinate
embedding in the independent parameter closure. -/
@[instance_reducible]
noncomputable def independentParameterClosureBaseAlgebra :
    letI := independentParameterClosureAlgebra F
    Algebra K (AlgebraicClosure (RatFunc F)) := by
  letI := independentParameterClosureAlgebra F
  infer_instance

/-- The two constructed coefficient actions have the actual tower. -/
theorem independentParameterClosureScalarTower :
    letI := independentParameterClosureAlgebra F
    letI := independentParameterClosureBaseAlgebra K F
    IsScalarTower K F (AlgebraicClosure (RatFunc F)) := by
  letI := independentParameterClosureAlgebra F
  letI := independentParameterClosureBaseAlgebra K F
  infer_instance

/-- The chosen parameter remains transcendental over the whole
source-coordinate field in the chosen algebraic closure. -/
theorem independentParameterClosure_variable_transcendental :
    letI := independentParameterClosureAlgebra F
    Transcendental F (algebraMap (RatFunc F) (AlgebraicClosure (RatFunc F)) RatFunc.X) := by
  letI := independentParameterClosureAlgebra F
  let : IsScalarTower F (RatFunc F) (AlgebraicClosure (RatFunc F)) := inferInstance
  exact (transcendental_algebraMap_iff (algebraMap (RatFunc F)
    (AlgebraicClosure (RatFunc F))).injective).mpr RatFunc.transcendental_X

variable {C E : Type*} [Field C] [Field E] [Algebra K C] [Algebra C E]
  [Algebra.IsAlgebraic C E]

/-- The actual algebraic parameter coefficients have a common
realization with an independent source parameter, with all original
constants and coefficient algebraicity preserved. -/
theorem algebraic_parameter_coefficients_construct_independent_realization
    (e : RatFunc K ≃ₐ[K] C) :
    letI := independentParameterClosureAlgebra F
    letI := independentParameterClosureBaseAlgebra K F
    ∃ (φ : RatFunc K →ₐ[K] AlgebraicClosure (RatFunc F))
      (σ : E →+* AlgebraicClosure (RatFunc F)),
      Transcendental F (φ RatFunc.X) ∧
      (∀ c : C, σ (algebraMap C E c) = φ (e.symm c)) ∧
      (∀ k : K, σ (algebraMap C E (algebraMap K C k)) =
        algebraMap K (AlgebraicClosure (RatFunc F)) k) ∧
      (letI : Algebra (RatFunc K) (AlgebraicClosure (RatFunc F)) := φ.toRingHom.toAlgebra
       ∀ a : E, IsAlgebraic (RatFunc K) (σ a)) := by
  letI := independentParameterClosureAlgebra F
  letI := independentParameterClosureBaseAlgebra K F
  let : IsScalarTower K F (AlgebraicClosure (RatFunc F)) := independentParameterClosureScalarTower K F
  let t := algebraMap (RatFunc F) (AlgebraicClosure (RatFunc F)) RatFunc.X
  have ht : Transcendental F t := independentParameterClosure_variable_transcendental F
  let φ := transcendentalParameterFieldHom t (ht.of_tower_top (K := K))
  let g : C →ₐ[K] AlgebraicClosure (RatFunc F) := φ.comp e.symm.toAlgHom
  let : Algebra C (AlgebraicClosure (RatFunc F)) := g.toRingHom.toAlgebra
  let σ : E →ₐ[C] AlgebraicClosure (RatFunc F) := IsAlgClosed.lift
  refine ⟨φ, σ.toRingHom, ?_, ?_, ?_, ?_⟩
  · rw [transcendentalParameterFieldHom_X]
    exact ht
  · intro c
    exact σ.commutes c
  · intro k
    exact (σ.commutes (algebraMap K C k)).trans (g.commutes k)
  · let : Algebra (RatFunc K) (AlgebraicClosure (RatFunc F)) := φ.toRingHom.toAlgebra
    intro a
    have hcomp : (algebraMap (RatFunc K) (AlgebraicClosure (RatFunc F))).comp e.symm.toRingHom =
        σ.toRingHom.comp (algebraMap C E) := by
      ext c
      exact (σ.commutes c).symm
    exact (Algebra.IsAlgebraic.isAlgebraic (R := C) a).ringHom_of_comp_eq
      e.symm.toRingHom σ.toRingHom e.symm.injective hcomp

end DimensionFourDependence
