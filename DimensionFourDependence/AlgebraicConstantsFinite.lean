import DimensionFourDependence.OutputCoordinates
import Mathlib.RingTheory.Algebraic.Integral

/-! # Algebraic constants inside a finite rational-function extension are finite

Algebraic coefficient extension preserves the rank of rational function
fields. Independent transcendental coordinates stay independent over
algebraic constants, so their rational function field embeds in the
ambient field. A finite-dimensional ambient rational extension therefore
bounds the coefficient extension and makes its algebraic constants finite.
-/

namespace DimensionFourDependence

universe u

variable {K C E : Type u} [Field K] [Field C] [Field E]
  [Algebra K C] [Algebra C E] [Algebra K E] [IsScalarTower K C E]
  [Algebra.IsAlgebraic K C] {n : ℕ}

attribute [local instance] MvPolynomial.algebraMvPolynomial FractionRing.liftAlgebra

/-- An algebraic coefficient extension in a field finite over an
actual rational-coordinate field is itself finite. The coefficient
rational-function-field embedding and scalar compatibility are proved. -/
theorem algebraic_constants_finite_of_finite_rational_extension
    (Y : Fin n → E) (hY : AlgebraicIndependent K Y)
    (hfinite : letI : Algebra (FractionRing (MvPolynomial (Fin n) K)) E :=
        (rationalOutputHom Y hY).toRingHom.toAlgebra
      Module.Finite (FractionRing (MvPolynomial (Fin n) K)) E) : Module.Finite K C := by
  let B := FractionRing (MvPolynomial (Fin n) K)
  let S := FractionRing (MvPolynomial (Fin n) C)
  let g : B →ₐ[K] E := rationalOutputHom Y hY
  let : Algebra B E := g.toRingHom.toAlgebra
  let : Module.Finite B E := hfinite
  have hYC : AlgebraicIndependent C Y := hY.extendScalars C
  let f : S →ₐ[C] E := rationalOutputHom Y hYC
  have hcomp : f.toRingHom.comp (algebraMap B S) = g.toRingHom := by
    apply IsFractionRing.ringHom_ext (A := MvPolynomial (Fin n) K)
    intro p
    have hpol : (f.toRingHom.comp (algebraMap B S)).comp (algebraMap (MvPolynomial (Fin n) K) B) =
        g.toRingHom.comp (algebraMap (MvPolynomial (Fin n) K) B) := by
      apply MvPolynomial.ringHom_ext
      · intro k
        change f (algebraMap B S (algebraMap K B k)) = g (algebraMap K B k)
        rw [← IsScalarTower.algebraMap_apply K B S]
        exact (f.restrictScalars K).commutes k |>.trans (g.commutes k).symm
      · intro i
        have hX : algebraMap B S (rationalCoordinate (K := K) i) =
            rationalCoordinate (K := C) i := by
          change algebraMap B S (algebraMap (MvPolynomial (Fin n) K) B (MvPolynomial.X i)) = _
          rw [← IsScalarTower.algebraMap_apply (MvPolynomial (Fin n) K) B S,
            IsScalarTower.algebraMap_apply (MvPolynomial (Fin n) K) (MvPolynomial (Fin n) C) S]
          rw [MvPolynomial.algebraMap_def, MvPolynomial.map_X]
          rfl
        change f (algebraMap B S (rationalCoordinate (K := K) i)) = g (rationalCoordinate (K := K) i)
        rw [hX, rationalOutputHom_coordinate, rationalOutputHom_coordinate]
    exact RingHom.congr_fun hpol p
  let fB : S →ₐ[B] E :=
    { f.toRingHom with
      commutes' := fun b => RingHom.congr_fun hcomp b }
  have hSfinite : Module.Finite B S := FiniteDimensional.of_injective fB.toLinearMap fB.injective
  have hrank : Module.rank B S = Module.rank K C := by
    simpa using
      (Algebra.IsAlgebraic.rank_fractionRing_mvPolynomial (R := K) (S := C) (Fin n))
  apply Module.rank_lt_aleph0_iff.mp
  rw [← hrank]
  exact Module.rank_lt_aleph0 B S

end DimensionFourDependence
