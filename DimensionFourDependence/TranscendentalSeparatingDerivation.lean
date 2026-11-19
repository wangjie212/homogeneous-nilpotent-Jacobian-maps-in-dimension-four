import DimensionFourDependence.RationalParameterDerivation
import DimensionFourDependence.AlgebraicDifferential
import Mathlib.RingTheory.AlgebraicIndependent.Adjoin

/-! # A derivation separating any transcendental parameter

Extend a parameter to a transcendence basis, differentiate its rational
coordinate field, and extend through the algebraic remainder. This will
detect the parameter differential on the actual image-cone tangent space.
-/

namespace DimensionFourDependence

open MvPolynomial

variable {K : Type*} [Field K] {σ : Type*}

/-- A bundled coordinate derivative for a rational function field in
an arbitrary set of variables, including a transcendence basis. -/
noncomputable def fractionCoordinateDerivation (j : σ) :
    Derivation K (FractionRing (MvPolynomial σ K)) (FractionRing (MvPolynomial σ K)) where
  toLinearMap :=
    { toFun := fracDeriv (K := K) j
      map_add' := fracDeriv_add j
      map_smul' := by
        intro c x
        simp only [RingHom.id_apply, Algebra.smul_def]
        rw [fracDeriv_mul, fracDeriv_algebraMap_field, mul_zero, add_zero] }
  map_one_eq_zero' := fracDeriv_one j
  leibniz' := fracDeriv_mul j

theorem fractionCoordinateDerivation_polynomial (j : σ) (p : MvPolynomial σ K) :
    fractionCoordinateDerivation (K := K) j
        (algebraMap (MvPolynomial σ K) (FractionRing (MvPolynomial σ K)) p) =
      algebraMap (MvPolynomial σ K) (FractionRing (MvPolynomial σ K)) (pderiv j p) :=
  fracDeriv_algebraMap j p

theorem fractionCoordinateDerivation_self (j : σ) :
    fractionCoordinateDerivation (K := K) j
      (algebraMap (MvPolynomial σ K) (FractionRing (MvPolynomial σ K)) (X j)) = 1 := by
  rw [fractionCoordinateDerivation_polynomial, pderiv_X_self, map_one]

variable {F : Type*} [Field F] [Algebra K F] [CharZero K]

/-- Every transcendental element of a characteristic-zero field
extension has a separating derivation, with value exactly one. No
finite-generation or smoothness hypothesis is supplied. -/
theorem exists_derivation_apply_eq_one_of_transcendental
    (t : F) (ht : Transcendental K t) : ∃ D : Derivation K F F, D t = 1 := by
  classical
  let y : Fin 1 → F := fun _ => t
  have hy : AlgebraicIndependent K y :=
    (algebraicIndependent_singleton_iff (R := K) (x := y) 0).mpr ht
  have hsingle : AlgebraicIndepOn K id ({t} : Set F) := by
    have h := hy.coe_range
    have he : Set.range y = ({t} : Set F) := by ext x; simp [y]
    rwa [he] at h
  obtain ⟨B, hsub, hB⟩ := exists_isTranscendenceBasis_superset hsingle
  let b : B := ⟨t, hsub (Set.mem_singleton t)⟩
  let v : B → F := Subtype.val
  let E := IntermediateField.adjoin K (Set.range v)
  let e : FractionRing (MvPolynomial B K) ≃ₐ[K] E := hB.1.aevalEquivField
  let δ : Derivation K E E := fieldDerivationConjugate e (fractionCoordinateDerivation (K := K) b)
  let : Algebra.IsAlgebraic E F := hB.isAlgebraic_field
  obtain ⟨D, hD, _hunique⟩ := existsUnique_derivation_extension_algebraic (L := F) δ
  let x : FractionRing (MvPolynomial B K) := algebraMap (MvPolynomial B K) _ (X b)
  have hx : (e x : F) = t := by
    change (hB.1.aevalEquivField (algebraMap (MvPolynomial B K) _ (X b)) : F) = t
    rw [AlgebraicIndependent.aevalEquivField_algebraMap_apply_coe, aeval_X]
  refine ⟨D, ?_⟩
  rw [← hx]
  change D (algebraMap E F (e x)) = 1
  rw [hD, fieldDerivationConjugate_apply]
  change algebraMap E F (e (fractionCoordinateDerivation b (algebraMap (MvPolynomial B K) _ (X b)))) = 1
  rw [fractionCoordinateDerivation_self, map_one, map_one]

end DimensionFourDependence
