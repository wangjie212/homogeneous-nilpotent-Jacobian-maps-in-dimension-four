import DimensionFourDependence.Defs

/-! # A finite projection has a nonzero base center at a nonfield local ring

If the contraction of the local maximal ideal were zero, every nonzero
base element would be a unit. The base fraction field would then act on
the local ring. A finite function-field extension makes that local ring
algebraic, hence integral, over the base field and forces it to be a field.
For a one-variable polynomial base this constructs the irreducible
polynomial at the original local center.
-/

namespace DimensionFourDependence

set_option synthInstance.maxHeartbeats 100000
set_option maxHeartbeats 2000000

variable {R K B L : Type*} [CommRing R] [IsDomain R] [Field K]
  [Algebra R K] [IsFractionRing R K]
  [CommRing B] [IsDomain B] [IsLocalRing B]
  [Field L] [Algebra K L] [Module.Finite K L]
  [Algebra R B] [Algebra R L] [Algebra B L] [IsFractionRing B L]
  [IsScalarTower R K L] [IsScalarTower R B L]

include K L in
/-- A nonfield local ring in a finite extension of the base fraction
field has nonzero contraction of its actual maximal ideal. -/
theorem finite_projection_local_center_ne_bot
    (hmax : IsLocalRing.maximalIdeal B ≠ ⊥) :
    (IsLocalRing.maximalIdeal B).under R ≠ ⊥ := by
  intro hzero
  have hunits (r : R) (hr : r ≠ 0) : IsUnit (algebraMap R B r) := by
    apply IsLocalRing.notMem_maximalIdeal.mp
    intro hm
    have hmem : r ∈ (IsLocalRing.maximalIdeal B).under R := hm
    rw [hzero, Ideal.mem_bot] at hmem
    exact hr hmem
  let g : K →ₐ[R] B := IsLocalization.liftAlgHom
    (M := nonZeroDivisors R) (f := Algebra.ofId R B)
    (fun r => hunits r (mem_nonZeroDivisors_iff_ne_zero.mp r.property))
  let : Algebra K B := g.toRingHom.toAlgebra
  let : IsScalarTower R K B :=
    IsScalarTower.of_algebraMap_eq (fun r => (g.commutes r).symm)
  have hmaps : (algebraMap B L).comp g.toRingHom = algebraMap K L := by
    apply IsLocalization.ringHom_ext (nonZeroDivisors R)
    apply RingHom.ext
    intro r
    change algebraMap B L (g (algebraMap R K r)) =
      algebraMap K L (algebraMap R K r)
    rw [g.commutes, ← IsScalarTower.algebraMap_apply R B L,
      ← IsScalarTower.algebraMap_apply R K L]
  let : IsScalarTower K B L := IsScalarTower.of_algebraMap_eq
    (fun x => (RingHom.congr_fun hmaps x).symm)
  let : Algebra.IsAlgebraic K B := Algebra.IsAlgebraic.of_injective
    (IsScalarTower.toAlgHom K B L) (IsFractionRing.injective B L)
  have hfield : IsField B := isField_of_isIntegral_of_isField'
    (R := K) (S := B) (inferInstance : Field K).toIsField
  exact hmax (IsLocalRing.isField_iff_maximalIdeal_eq.mp hfield)

/-- A finite rational projection constructs an irreducible polynomial
whose original value lies in the actual nonfield local center. -/
theorem finite_rational_projection_exists_irreducible_center
    {k B L : Type*} [Field k] [CommRing B] [IsDomain B] [IsLocalRing B]
    [Field L] [Algebra (RatFunc k) L] [Module.Finite (RatFunc k) L]
    [Algebra (Polynomial k) B] [Algebra (Polynomial k) L]
    [Algebra B L] [IsFractionRing B L]
    [IsScalarTower (Polynomial k) (RatFunc k) L]
    [IsScalarTower (Polynomial k) B L]
    (hmax : IsLocalRing.maximalIdeal B ≠ ⊥) :
    ∃ p : Polynomial k, Irreducible p ∧
      algebraMap (Polynomial k) B p ∈ IsLocalRing.maximalIdeal B := by
  let J := (IsLocalRing.maximalIdeal B).under (Polynomial k)
  have hJ : J ≠ ⊥ := finite_projection_local_center_ne_bot
    (K := RatFunc k) (L := L) hmax
  let : J.IsPrime := inferInstanceAs
    (((IsLocalRing.maximalIdeal B).under (Polynomial k)).IsPrime)
  exact ⟨Submodule.IsPrincipal.generator J,
    (Submodule.IsPrincipal.prime_generator_of_isPrime J hJ).irreducible,
    Submodule.IsPrincipal.generator_mem J⟩

end DimensionFourDependence
